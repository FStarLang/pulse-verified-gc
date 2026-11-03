/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.Act — the worker's actions keep the invariant
///
/// `send`, `grey_push`, `accept` and `route`, each done by a worker that
/// holds one counted item (it is scanning, or has taken an entry):
///   * send and grey_push keep `core`, and keep `black_ok_but c0` for any c0;
///     after a send the entry's object is pending, or a flag is set; after
///     grey_push the object is not white;
///   * so accept and route, given an entry naming c0, turn
///     `black_ok_but (Some c0)` into `black_ok`.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.Act

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
open FStar.List.Tot { (@) }

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

module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module M1 = GC.Spec.MarkPar.Model
module I1 = GC.Spec.MarkPar.Inv
module Own = GC.Spec.MarkPar.Own
module LS = GC.Spec.MarkPar2.Lists

module U = GC.Spec.MarkPar2.Upd

let wk_ok_recolour (k: cfg) (g h: heap) (i: nat) (w: wk) (x: obj_addr) (c: color)
  : Lemma (requires wk_ok k g h i w /\ ~(L.memP x w.stack) /\
                    (match w.pc with Scan sc -> sc.M1.sobj <> x | _ -> True))
          (ensures wk_ok k g (set_object_color x h c) i w)
  = let aux (y: obj_addr) : Lemma (requires L.memP y w.stack) (ensures is_gray y (set_object_color x h c)) =
      Own.other_color h x y c in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    match w.pc with Scan sc -> Own.other_color h x sc.M1.sobj c | _ -> ()

let own_rec = U.own_rec
let own_len = U.own_len

/// ---------------------------------------------------------------------------
/// send
/// ---------------------------------------------------------------------------

let act_pre (k: cfg) (g: heap) (roots: list obj_addr) (t: state) (me: nat) (c0: option obj_addr) : prop =
  ctx k g roots /\ core k g roots t /\ black_ok_but k g t c0 /\ ~t.finished /\
  me < nr k /\ held (pc_of t me) == 1

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let send_full (k: cfg) (g: heap) (roots: list obj_addr) (t: state) (me: nat) (c0: option obj_addr)
  : Lemma (requires act_pre k g roots t me c0)
          (ensures (let t' = set_ovf t me in
                    core k g roots t' /\ black_ok_but k g t' c0 /\ flagged t' /\ ~t'.finished))
  = own_len k g t;
    U.old_eq t me;
    let w = U.old t me in
    let w' = { w with ovf = true } in
    let t' = U.upd t me w' t.heap t.count in
    assert (set_ovf t me == t');
    U.upd_wk t me w' t.heap t.count;
    U.own_others k g t me;
    own_rec k g t me w;
    U.own_upd_same k g t me w' t.count;
    U.busy_count t me;
    U.count_upd t me w' t.heap t.count;
    U.flagged_upd t me w' t.heap t.count;
    reveal_opaque (`%grey_ok) (grey_ok k g t');
    U.sound_upd g roots t me w' t.heap t.count;
    U.roots_upd g roots t t';
    U.fin_running t';
    U.keeps_upd k g t me w' t.heap t.count;
    black_keeps k g t t' c0
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let send_append (k: cfg) (g: heap) (roots: list obj_addr) (t: state) (me j: nat) (v: obj_addr)
    (c0: option obj_addr) (wj: wk)
  : Lemma (requires act_pre k g roots t me c0 /\ j < nr k /\ wk_of t j == Some wj /\
                    L.length wj.inbox < k.cap_q /\
                    entry_ok k g j v /\ M1.reachable g roots (resolve_object v g))
          (ensures (let t' = send k t me j v in
                    core k g roots t' /\ black_ok_but k g t' c0 /\
                    pending g t' (resolve_object v g) /\ ~t'.finished))
  = own_len k g t;
    U.old_eq t j;
    let wj' = { wj with inbox = wj.inbox @ [v] } in
    let n = t.count + 1 in
    let t' = U.upd t j wj' t.heap n in
    assert (send k t me j v == t');
    U.upd_wk t j wj' t.heap n;
    U.size_append wj v;
    U.own_others k g t j;
    own_rec k g t j wj;
    U.own_upd_same k g t j wj' n;
    U.busy_count t me;
    U.count_upd t j wj' t.heap n;
    U.flagged_upd t j wj' t.heap n;
    U.grey_upd k g t t';
    U.sound_upd g roots t j wj' t.heap n;
    U.roots_upd g roots t t';
    U.fin_running t';
    U.keeps_upd k g t j wj' t.heap n;
    black_keeps k g t t' c0;
    assert (holds t' j v)
#pop-options

let send_lemma (k: cfg) (g: heap) (roots: list obj_addr) (t: state) (me j: nat) (v: obj_addr)
    (c0: option obj_addr)
  : Lemma (requires act_pre k g roots t me c0 /\ j < nr k /\
                    entry_ok k g j v /\ M1.reachable g roots (resolve_object v g))
          (ensures (let t' = send k t me j v in
                    core k g roots t' /\ black_ok_but k g t' c0 /\
                    (pending g t' (resolve_object v g) \/ flagged t') /\ ~t'.finished))
  = own_len k g t;
    U.old_eq t j;
    let wj = U.old t j in
    if L.length wj.inbox >= k.cap_q then send_full k g roots t me c0
    else send_append k g roots t me j v c0 wj

/// ---------------------------------------------------------------------------
/// grey_push
/// ---------------------------------------------------------------------------

let push_pre (k: cfg) (g: heap) (roots: list obj_addr) (t: state) (me: nat) (c0: option obj_addr)
    (c: obj_addr) : prop =
  act_pre k g roots t me c0 /\
  Seq.mem c (objs g) /\ own k c == me /\ ~(is_blue c g) /\ M1.reachable g roots c

/// Greying a white c keeps every worker's record.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let grey_records (k: cfg) (g: heap) (t: state) (c: obj_addr)
  : Lemma (requires own_ok k g t /\ is_white c t.heap)
          (ensures forall (i: nat) (w: wk). wk_of t i == Some w ==>
                     wk_ok k g (set_object_color c t.heap Gray) i w /\ ~(L.memP c w.stack))
  = let aux (i: nat) (w: wk)
      : Lemma (requires wk_of t i == Some w)
              (ensures wk_ok k g (set_object_color c t.heap Gray) i w /\ ~(L.memP c w.stack))
      = own_rec k g t i w;
        colors c t.heap;
        (match w.pc with Scan sc -> colors sc.M1.sobj t.heap | _ -> ());
        wk_ok_recolour k g t.heap i w c Gray
    in
    FStar.Classical.forall_intro_2 (fun i w -> FStar.Classical.move_requires (aux i) w)
#pop-options

/// The heap after greying a white, non-blue enumerated c.
let grey_heap (k: cfg) (g: heap) (t: state) (c: obj_addr)
  : Lemma (requires own_ok k g t /\ is_white c t.heap /\ Seq.mem c (objs g) /\ ~(is_blue c g))
          (ensures (let h' = makeGray_x c t.heap in
                    h' == set_object_color c t.heap Gray /\ recoloured g h' /\ is_gray c h' /\
                    (forall (x: obj_addr). x <> c ==>
                       is_gray x h' == is_gray x t.heap /\ is_black x h' == is_black x t.heap /\
                       is_white x h' == is_white x t.heap)))
  = U.own_heap k g t;
    makeGray_eq c t.heap;
    recoloured_makeGray g t.heap c;
    makeGray_is_gray c t.heap;
    I1.others_keep t.heap c Gray
let push_record (k: cfg) (g h: heap) (me: nat) (w: wk) (c: obj_addr)
  : Lemma (requires wk_ok k g h me w /\ ~(L.memP c w.stack) /\ Seq.mem c (objs g) /\
                    own k c == me /\ is_gray c h /\ ~(Idle? w.pc))
          (ensures wk_ok k g h me { w with stack = c :: w.stack } /\ wk_ok k g h me { w with ovf = true })
  = ()

/// The facts both cases of grey_push need.
let grey_ctx (k: cfg) (g: heap) (roots: list obj_addr) (t: state) (me: nat) (c0: option obj_addr)
    (c: obj_addr) (w: wk) (h': heap) : prop =
  push_pre k g roots t me c0 c /\ is_white c t.heap /\
  L.length t.wks == nr k /\ wk_of t me == Some w /\ U.old t me == w /\
  h' == set_object_color c t.heap Gray /\ recoloured g h' /\ is_gray c h' /\
  (forall (x: obj_addr). x <> c ==>
     is_gray x h' == is_gray x t.heap /\ is_black x h' == is_black x t.heap /\
     is_white x h' == is_white x t.heap) /\
  (forall (i: nat) (wi: wk). wk_of t i == Some wi ==> wk_ok k g h' i wi /\ ~(L.memP c wi.stack)) /\
  t.count >= 1 /\ ~(Stopped? w.pc) /\ ~(Idle? w.pc)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let grey_push_case (k: cfg) (g: heap) (roots: list obj_addr) (t: state) (me: nat)
    (c0: option obj_addr) (c: obj_addr) (w: wk) (h': heap) (full: bool)
  : Lemma (requires grey_ctx k g roots t me c0 c w h')
          (ensures (let w' = if full then { w with ovf = true } else { w with stack = c :: w.stack } in
                    let n = if full then t.count else t.count + 1 in
                    let t' = U.upd t me w' h' n in
                    core k g roots t' /\ black_ok_but k g t' c0 /\
                    ~(is_white c t'.heap) /\ ~t'.finished))
  = let w' = if full then { w with ovf = true } else { w with stack = c :: w.stack } in
    let n = if full then t.count else t.count + 1 in
    let t' = U.upd t me w' h' n in
    U.upd_wk t me w' h' n;
    push_record k g h' me w c;
    U.own_upd k g t me w' h' n;
    U.count_upd t me w' h' n;
    U.flagged_upd t me w' h' n;
    colors c h';
    U.grey_upd k g t t';
    U.sound_upd g roots t me w' h' n;
    U.roots_upd g roots t t';
    U.fin_running t';
    U.keeps_upd k g t me w' h' n;
    black_keeps k g t t' c0
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let grey_push_white (k: cfg) (g: heap) (roots: list obj_addr) (t: state) (me: nat)
    (c0: option obj_addr) (c: obj_addr)
  : Lemma (requires push_pre k g roots t me c0 c /\ is_white c t.heap)
          (ensures (let t' = grey_push k t me c in
                    core k g roots t' /\ black_ok_but k g t' c0 /\
                    ~(is_white c t'.heap) /\ ~t'.finished))
  = own_len k g t;
    U.old_eq t me;
    let w = U.old t me in
    let h' = makeGray_x c t.heap in
    grey_heap k g t c;
    grey_records k g t c;
    U.busy_count t me;
    let full = L.length w.stack >= k.cap_s in
    grey_push_case k g roots t me c0 c w h' full;
    let w' = if full then { w with ovf = true } else { w with stack = c :: w.stack } in
    let n = if full then t.count else t.count + 1 in
    assert (grey_push k t me c == U.upd t me w' h' n)
#pop-options

let grey_push_lemma (k: cfg) (g: heap) (roots: list obj_addr) (t: state) (me: nat)
    (c0: option obj_addr) (c: obj_addr)
  : Lemma (requires push_pre k g roots t me c0 c)
          (ensures (let t' = grey_push k t me c in
                    core k g roots t' /\ black_ok_but k g t' c0 /\
                    ~(is_white c t'.heap) /\ ~t'.finished))
  = if is_white_x c t.heap then grey_push_white k g roots t me c0 c

/// ---------------------------------------------------------------------------
/// accept and route
/// ---------------------------------------------------------------------------

let entry_facts (k: cfg) (g: heap) (roots: list obj_addr) (t: state) (c0: obj_addr)
  : Lemma (requires ctx k g roots /\ Seq.mem c0 (objs g) /\ ~(is_blue c0 g))
          (ensures entry_ok k g (own k c0) c0 /\ resolve_object c0 g == c0 /\ own k c0 < nr k)
  = ctx_elim k g roots;
    resolve_self g c0;
    own_lt k c0

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let accept_lemma (k: cfg) (g: heap) (roots: list obj_addr) (t: state) (me: nat) (v c0: obj_addr)
  : Lemma (requires act_pre k g roots t me (Some c0) /\ entry_ok k g me v /\
                    resolve_object v g == c0 /\ M1.reachable g roots c0)
          (ensures (let t' = accept k t me v in core k g roots t' /\ black_ok k g t' /\ ~t'.finished))
  = reveal_opaque (`%own_ok) (own_ok k g t);
    resolve_recoloured g t.heap v;
    entry_facts k g roots t c0;
    let o = own k c0 in
    if o <> me then begin
      send_lemma k g roots t me o c0 (Some c0);
      black_cover k g (send k t me o c0) c0
    end else begin
      grey_push_lemma k g roots t me (Some c0) c0;
      black_cover k g (grey_push k t me c0) c0
    end
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let route_lemma (k: cfg) (g: heap) (roots: list obj_addr) (t: state) (me: nat) (v c0: obj_addr)
  : Lemma (requires act_pre k g roots t me (Some c0) /\
                    Seq.mem c0 (objs g) /\ ~(is_blue c0 g) /\
                    resolve_object v g == c0 /\ M1.reachable g roots c0)
          (ensures (let t' = route k t me v in core k g roots t' /\ black_ok k g t' /\ ~t'.finished))
  = let o = own k v in
    own_lt k v;
    if o = me then accept_lemma k g roots t me v c0
    else begin
      send_lemma k g roots t me o v (Some c0);
      black_cover k g (send k t me o v) c0
    end
#pop-options
