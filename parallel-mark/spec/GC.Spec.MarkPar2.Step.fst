/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.Step — every worker step keeps the invariant
///
/// One lemma per case of `wstep`: a pop, a take, a take that finds the
/// inbox empty, a counter read (stop or look again), a field scanned, a
/// taken entry accepted, and the subtraction at the end.  A scan and an
/// accept go through an intermediate state, in which the worker has moved
/// on but not yet routed the entry; there `black_ok_but (Some c0)` holds,
/// and `GC.Spec.MarkPar2.Act` finishes the job.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.Step

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
module A = GC.Spec.MarkPar2.Act

/// The setting of one worker step: worker i, record w, marking not done.
let step_pre (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk) : prop =
  ctx k g roots /\ inv k g roots s /\ ~s.finished /\ wk_of s i == Some w /\
  L.length s.wks == nr k /\ i < L.length s.wks /\ U.old s i == w

/// ---------------------------------------------------------------------------
/// Pop
/// ---------------------------------------------------------------------------

let pop_pc (s: state) (x: obj_addr) : pc =
  let ws = wosize_x x s.heap in
  if is_no_scan_x x s.heap || U64.v ws = 0 then Finish
  else Scan { M1.sobj = x; M1.snext = 1UL; M1.sws = ws }

/// What popping x gives: x black, every other colour kept.
let pop_heap (k: cfg) (g: heap) (s: state) (x: obj_addr)
  : Lemma (requires own_ok k g s /\ Seq.mem x (objs g) /\ is_gray x s.heap)
          (ensures (let h' = makeBlack_x x s.heap in
                    h' == set_object_color x s.heap Black /\ recoloured g h' /\ is_black x h' /\
                    wosize_x x s.heap == wosize_of_object x g /\
                    is_no_scan_x x s.heap == is_no_scan x g /\
                    (forall (y: obj_addr). y <> x ==>
                       is_gray y h' == is_gray y s.heap /\ is_black y h' == is_black y s.heap /\
                       is_white y h' == is_white y s.heap)))
  = U.own_heap k g s;
    colors x s.heap;
    makeBlack_eq x s.heap;
    recoloured_makeBlack g s.heap x;
    makeBlack_is_black x s.heap;
    recoloured_wosize g s.heap x;
    recoloured_no_scan g s.heap x;
    I1.others_keep s.heap x Black

/// Every other worker's record survives blackening x.
let pop_others (k: cfg) (g: heap) (s: state) (i: nat) (x: obj_addr)
  : Lemma (requires own_ok k g s /\ own k x == i /\ is_gray x s.heap)
          (ensures forall (j: nat) (wj: wk). j <> i /\ wk_of s j == Some wj ==>
                     wk_ok k g (set_object_color x s.heap Black) j wj)
  = let aux (j: nat) (wj: wk)
      : Lemma (requires j <> i /\ wk_of s j == Some wj)
              (ensures wk_ok k g (set_object_color x s.heap Black) j wj)
      = U.own_rec k g s j wj;
        colors x s.heap;
        (match wj.pc with Scan sc -> colors sc.M1.sobj s.heap | _ -> ());
        A.wk_ok_recolour k g s.heap j wj x Black
    in
    FStar.Classical.forall_intro_2 (fun j wj -> FStar.Classical.move_requires (aux j) wj)

let pop_record (k: cfg) (g: heap) (s: state) (i: nat) (w: wk) (x: obj_addr) (rest: list obj_addr)
  : Lemma (requires own_ok k g s /\ wk_of s i == Some w /\ w.stack == x :: rest)
          (ensures Seq.mem x (objs g) /\ own k x == i /\ is_gray x s.heap /\ ~(L.memP x rest) /\
                   wk_ok k g (set_object_color x s.heap Black) i
                     { w with stack = rest; pc = pop_pc s x })
  = U.own_rec k g s i w;
    pop_heap k g s x;
    colors x s.heap;
    A.wk_ok_recolour k g s.heap i { w with stack = rest; pc = Loop } x Black

/// The popped object's fields are covered by the scan that starts.
let pop_black (k: cfg) (g: heap) (s s': state) (i: nat) (x: obj_addr) (rest: list obj_addr)
  : Lemma (requires black_ok k g s /\ own k x == i /\ pc_of s i == Loop /\
                    pc_of s' i == pop_pc s x /\
                    wosize_x x s.heap == wosize_of_object x g /\ is_no_scan_x x s.heap == is_no_scan x g /\
                    (forall (j: nat). j <> i ==> pc_of s' j == pc_of s j) /\
                    (forall (y: obj_addr). y <> x ==> is_black y s'.heap == is_black y s.heap) /\
                    (forall (y: obj_addr). ~(is_white y s.heap) ==> ~(is_white y s'.heap)) /\
                    (forall (j: nat) (v: obj_addr). holds s j v ==> holds s' j v) /\
                    flagged s' == flagged s)
          (ensures black_ok k g s')
  = reveal_opaque (`%black_ok_but) (black_ok_but k g s' None);
    let aux (y: obj_addr) (j: U64.t{U64.v j >= 1})
      : Lemma (requires I1.is_field g y j /\ is_black y s'.heap)
              (ensures covered k g s' (I1.field_target g y j) y (U64.v j))
      = if y = x then ()
        else begin
          black_ok_at k g s None y j;
          let c = I1.field_target g y j in
          FStar.Classical.move_requires (keeps_pending k g s s') c;
          assert (pending g s c ==> pending g s' c)
        end
    in
    FStar.Classical.forall_intro_2 (fun y j -> FStar.Classical.move_requires (aux y) j)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let step_pop (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk)
    (x: obj_addr) (rest: list obj_addr)
  : Lemma (requires step_pre k g roots s i w /\ w.pc == Loop /\ w.stack == x :: rest)
          (ensures inv k g roots (wstep k s i))
  = let h' = makeBlack_x x s.heap in
    pop_record k g s i w x rest;
    pop_heap k g s x;
    pop_others k g s i x;
    let w' = { w with stack = rest; pc = pop_pc s x } in
    let s' = U.upd s i w' h' s.count in
    assert (wstep k s i == s');
    U.upd_wk s i w' h' s.count;
    U.own_upd k g s i w' h' s.count;
    U.count_pos s i;
    U.count_upd s i w' h' s.count;
    U.flagged_upd s i w' h' s.count;
    colors x h';
    U.grey_upd k g s s';
    U.sound_upd g roots s i w' h' s.count;
    U.roots_upd g roots s s';
    U.fin_running s';
    pop_black k g s s' i x rest
#pop-options

/// ---------------------------------------------------------------------------
/// Take, stop, finish
/// ---------------------------------------------------------------------------

/// A step that changes only worker i's record, keeping the heap, the
/// stack, the flag and the entries held: core and black_ok carry over.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let step_rec (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w w': wk) (n: nat)
  : Lemma (requires step_pre k g roots s i w /\ wk_ok k g s.heap i w' /\
                    w'.stack == w.stack /\ w'.ovf == w.ovf /\ ~(Scan? w.pc) /\
                    n + LS.size w == s.count + LS.size w' /\
                    (n == 0 \/ s.count > 0) /\ (Stopped? w'.pc ==> n == 0) /\
                    (forall (v: obj_addr). U.holds_w w' v <==> U.holds_w w v))
          (ensures inv k g roots (U.upd s i w' s.heap n))
  = let s' = U.upd s i w' s.heap n in
    U.upd_wk s i w' s.heap n;
    U.own_others k g s i;
    U.own_upd_same k g s i w' n;
    U.count_upd s i w' s.heap n;
    U.flagged_upd s i w' s.heap n;
    U.grey_upd k g s s';
    U.sound_upd g roots s i w' s.heap n;
    U.roots_upd g roots s s';
    U.fin_running s';
    U.keeps_upd k g s i w' s.heap n;
    black_keeps k g s s' None
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let step_take (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk)
    (v: obj_addr) (rest: list obj_addr)
  : Lemma (requires step_pre k g roots s i w /\ w.pc == Loop /\ w.stack == [] /\ w.inbox == v :: rest)
          (ensures inv k g roots (wstep k s i))
  = let w' = { w with inbox = rest; pc = Got v } in
    U.own_rec k g s i w;
    U.count_pos s i;
    assert (wstep k s i == U.upd s i w' s.heap s.count);
    step_rec k g roots s i w w' s.count
#pop-options

/// try_take found the inbox empty.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let step_empty (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk)
  : Lemma (requires step_pre k g roots s i w /\ w.pc == Loop /\ w.stack == [] /\ w.inbox == [])
          (ensures inv k g roots (wstep k s i))
  = let w' = { w with pc = Idle } in
    U.own_rec k g s i w;
    assert (wstep k s i == U.upd s i w' s.heap s.count);
    step_rec k g roots s i w w' s.count
#pop-options

/// The counter read: at 0 stop, otherwise look again.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let step_idle (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk)
  : Lemma (requires step_pre k g roots s i w /\ w.pc == Idle)
          (ensures inv k g roots (wstep k s i))
  = let w' = { w with pc = if s.count = 0 then Stopped else Loop } in
    U.own_rec k g s i w;
    assert (wstep k s i == U.upd s i w' s.heap s.count);
    step_rec k g roots s i w w' s.count
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let step_finish (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk)
  : Lemma (requires step_pre k g roots s i w /\ w.pc == Finish)
          (ensures inv k g roots (wstep k s i))
  = let w' = { w with pc = Loop } in
    U.own_rec k g s i w;
    U.count_pos s i;
    let n : nat = s.count - 1 in
    assert (wstep k s i == U.upd s i w' s.heap n);
    step_rec k g roots s i w w' n
#pop-options

/// ---------------------------------------------------------------------------
/// Scan
/// ---------------------------------------------------------------------------

let next_pc (sc: M1.scanning) : pc =
  match M1.next_field sc with Some sc' -> Scan sc' | None -> Finish

/// The field just read, in g.
let scan_field (k: cfg) (g: heap) (s: state) (i: nat) (w: wk) (sc: M1.scanning)
  : Lemma (requires own_ok k g s /\ wk_of s i == Some w /\ w.pc == Scan sc)
          (ensures Seq.mem sc.M1.sobj (objs g) /\ own k sc.M1.sobj == i /\
                   is_black sc.M1.sobj s.heap /\ ~(is_blue sc.M1.sobj g) /\
                   sc.M1.sws == wosize_of_object sc.M1.sobj g /\
                   U64.v sc.M1.snext <= U64.v sc.M1.sws /\
                   get_field_x s.heap sc.M1.sobj sc.M1.snext == HeapGraph.get_field g sc.M1.sobj sc.M1.snext /\
                   (HeapGraph.is_pointer_field (HeapGraph.get_field g sc.M1.sobj sc.M1.snext) ==>
                      I1.is_field g sc.M1.sobj sc.M1.snext) /\
                   wk_ok k g s.heap i { w with pc = next_pc sc })
  = U.own_rec k g s i w;
    U.own_heap k g s;
    colors sc.M1.sobj s.heap;
    recoloured_blue g s.heap sc.M1.sobj

/// A field other than the one just read keeps its unscanned cover.
let scan_unscanned (k: cfg) (g: heap) (s s0: state) (i: nat) (sc: M1.scanning)
    (y: obj_addr) (j: U64.t{U64.v j >= 1})
  : Lemma (requires unscanned k s y (U64.v j) /\ own k sc.M1.sobj == i /\ pc_of s i == Scan sc /\
                    pc_of s0 i == next_pc sc /\ sc.M1.sws == wosize_of_object sc.M1.sobj g /\
                    (forall (j: nat). j <> i ==> pc_of s0 j == pc_of s j) /\
                    (y == sc.M1.sobj ==> U64.v j <= U64.v sc.M1.sws) /\
                    ~(y == sc.M1.sobj /\ U64.v j == U64.v sc.M1.snext))
          (ensures unscanned k s0 y (U64.v j))
  = ()

let scan_cover (k: cfg) (g: heap) (s s0: state) (i: nat) (sc: M1.scanning) (c0: option obj_addr)
    (y: obj_addr) (j: U64.t{U64.v j >= 1})
  : Lemma (requires covered k g s (I1.field_target g y j) y (U64.v j) /\
                    own k sc.M1.sobj == i /\ pc_of s i == Scan sc /\
                    pc_of s0 i == next_pc sc /\ sc.M1.sws == wosize_of_object sc.M1.sobj g /\
                    (forall (j: nat). j <> i ==> pc_of s0 j == pc_of s j) /\
                    s0.heap == s.heap /\
                    (forall (j: nat) (v: obj_addr). holds s j v ==> holds s0 j v) /\
                    flagged s0 == flagged s /\ I1.is_field g y j /\
                    (I1.is_field g sc.M1.sobj sc.M1.snext ==>
                       c0 == Some (I1.field_target g sc.M1.sobj sc.M1.snext)))
          (ensures covered k g s0 (I1.field_target g y j) y (U64.v j) \/
                   c0 == Some (I1.field_target g y j))
  = let c = I1.field_target g y j in
    if y = sc.M1.sobj && U64.v j = U64.v sc.M1.snext then U64.v_inj j sc.M1.snext
    else begin
      FStar.Classical.move_requires (scan_unscanned k g s s0 i sc y) j;
      assert (pending g s c ==> pending g s0 c)
    end

/// After moving past field f of x, the fields are covered except f itself.
let scan_black (k: cfg) (g: heap) (s s0: state) (i: nat) (sc: M1.scanning) (c0: option obj_addr)
  : Lemma (requires black_ok k g s /\ own k sc.M1.sobj == i /\ pc_of s i == Scan sc /\
                    pc_of s0 i == next_pc sc /\ sc.M1.sws == wosize_of_object sc.M1.sobj g /\
                    (forall (j: nat). j <> i ==> pc_of s0 j == pc_of s j) /\
                    s0.heap == s.heap /\
                    (forall (j: nat) (v: obj_addr). holds s j v ==> holds s0 j v) /\
                    flagged s0 == flagged s /\
                    (I1.is_field g sc.M1.sobj sc.M1.snext ==>
                       c0 == Some (I1.field_target g sc.M1.sobj sc.M1.snext)))
          (ensures black_ok_but k g s0 c0)
  = reveal_opaque (`%black_ok_but) (black_ok_but k g s0 c0);
    let aux (y: obj_addr) (j: U64.t{U64.v j >= 1})
      : Lemma (requires I1.is_field g y j /\ is_black y s0.heap)
              (ensures covered k g s0 (I1.field_target g y j) y (U64.v j) \/
                       c0 == Some (I1.field_target g y j))
      = black_ok_at k g s None y j;
        scan_cover k g s s0 i sc c0 y j
    in
    FStar.Classical.forall_intro_2 (fun y j -> FStar.Classical.move_requires (aux y) j)

/// The state after moving past the field, before routing it.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let scan_mid (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk)
    (sc: M1.scanning) (c0: option obj_addr)
  : Lemma (requires step_pre k g roots s i w /\ w.pc == Scan sc /\
                    (I1.is_field g sc.M1.sobj sc.M1.snext ==>
                       c0 == Some (I1.field_target g sc.M1.sobj sc.M1.snext)))
          (ensures (let s0 = U.upd s i { w with pc = next_pc sc } s.heap s.count in
                    core k g roots s0 /\ black_ok_but k g s0 c0 /\ ~s0.finished /\
                    held (pc_of s0 i) == 1))
  = let w' = { w with pc = next_pc sc } in
    let s0 = U.upd s i w' s.heap s.count in
    scan_field k g s i w sc;
    U.upd_wk s i w' s.heap s.count;
    U.own_others k g s i;
    U.own_upd_same k g s i w' s.count;
    U.count_upd s i w' s.heap s.count;
    U.flagged_upd s i w' s.heap s.count;
    U.grey_upd k g s s0;
    U.sound_upd g roots s i w' s.heap s.count;
    U.roots_upd g roots s s0;
    U.fin_running s0;
    scan_black k g s s0 i sc c0
#pop-options

/// The object a scanned pointer field names: enumerated, non-blue,
/// reachable.
let scan_target (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (x: obj_addr)
    (j: U64.t{U64.v j >= 1})
  : Lemma (requires ctx k g roots /\ sound g roots s /\ I1.is_field g x j /\ is_black x s.heap)
          (ensures (let c = I1.field_target g x j in
                    Seq.mem c (objs g) /\ ~(is_blue c g) /\ M1.reachable g roots c))
  = reveal_opaque (`%ctx) (ctx k g roots);
    reveal_opaque (`%I1.ctx) (I1.ctx k.cs g roots);
    reveal_opaque (`%sound) (sound g roots s);
    I1.target_facts k.cs g roots x j

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let step_scan (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk) (sc: M1.scanning)
  : Lemma (requires step_pre k g roots s i w /\ w.pc == Scan sc)
          (ensures inv k g roots (wstep k s i))
  = let w' = { w with pc = next_pc sc } in
    let s0 = U.upd s i w' s.heap s.count in
    scan_field k g s i w sc;
    let x = sc.M1.sobj in
    let f = sc.M1.snext in
    let v = get_field_x s.heap x f in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let c0 = I1.field_target g x f in
      scan_mid k g roots s i w sc (Some c0);
      scan_target k g roots s x f;
      assert (resolve_object (v <: obj_addr) g == c0);
      A.route_lemma k g roots s0 i v c0;
      assert (wstep k s i == route k s0 i v)
    end else begin
      scan_mid k g roots s i w sc None;
      assert (wstep k s i == s0)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Accept a taken entry
/// ---------------------------------------------------------------------------

let got_black (k: cfg) (g: heap) (s s0: state) (i: nat) (v: obj_addr)
  : Lemma (requires black_ok k g s /\
                    (forall (x: obj_addr) (j: nat). unscanned k s x j ==> unscanned k s0 x j) /\
                    s0.heap == s.heap /\
                    (forall (j: nat) (u: obj_addr). holds s j u ==> holds s0 j u \/ (j == i /\ u == v)) /\
                    flagged s0 == flagged s)
          (ensures black_ok_but k g s0 (Some (resolve_object v g)))
  = reveal_opaque (`%black_ok_but) (black_ok_but k g s0 (Some (resolve_object v g)));
    let aux (y: obj_addr) (j: U64.t{U64.v j >= 1})
      : Lemma (requires I1.is_field g y j /\ is_black y s0.heap)
              (ensures covered k g s0 (I1.field_target g y j) y (U64.v j) \/
                       Some (resolve_object v g) == Some (I1.field_target g y j))
      = black_ok_at k g s None y j
    in
    FStar.Classical.forall_intro_2 (fun y j -> FStar.Classical.move_requires (aux y) j)

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let step_got (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk) (v: obj_addr)
  : Lemma (requires step_pre k g roots s i w /\ w.pc == Got v)
          (ensures inv k g roots (wstep k s i))
  = let w' = { w with pc = Finish } in
    let s0 = U.upd s i w' s.heap s.count in
    let c0 = resolve_object v g in
    U.own_rec k g s i w;
    reveal_opaque (`%sound) (sound g roots s);
    assert (holds s i v);
    U.upd_wk s i w' s.heap s.count;
    U.own_others k g s i;
    U.own_upd_same k g s i w' s.count;
    U.count_upd s i w' s.heap s.count;
    U.flagged_upd s i w' s.heap s.count;
    U.grey_upd k g s s0;
    U.sound_upd g roots s i w' s.heap s.count;
    U.roots_upd g roots s s0;
    U.fin_running s0;
    got_black k g s s0 i v;
    A.accept_lemma k g roots s0 i v c0;
    assert (wstep k s i == accept k s0 i v)
#pop-options

/// ---------------------------------------------------------------------------
/// Every worker step
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let wstep_inv (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat)
  : Lemma (requires ctx k g roots /\ inv k g roots s /\ ~s.finished)
          (ensures inv k g roots (wstep k s i))
  = U.own_len k g s;
    if i >= L.length s.wks then Own.nth_lt s.wks i
    else begin
      U.old_eq s i;
      let w = U.old s i in
      match w.pc with
      | Loop ->
        (match w.stack with
         | x :: rest -> step_pop k g roots s i w x rest
         | [] ->
           (match w.inbox with
            | v :: rest -> step_take k g roots s i w v rest
            | [] -> step_empty k g roots s i w))
      | Idle -> step_idle k g roots s i w
      | Scan sc -> step_scan k g roots s i w sc
      | Got v -> step_got k g roots s i w v
      | Finish -> step_finish k g roots s i w
      | Stopped -> ()
    end
#pop-options
