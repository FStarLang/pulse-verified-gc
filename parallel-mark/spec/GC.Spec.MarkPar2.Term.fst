/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.Term — every run ends
///
/// From any state a run reaches:
///   * an enabled event lowers the measure by at least 1 (`enabled_drops`);
///   * an event that is not enabled changes nothing, or is a spin step: a
///     worker with nothing to do, while the counter is not 0, moves between
///     Loop and Idle, which keeps the measure, and its next step undoes it
///     (`disabled_spin`);
///   * nothing is enabled exactly when marking is done (`enabled_nil`): if
///     marking is not done and some worker has not stopped, the counter
///     names a worker that can move; if every worker has stopped, the main
///     thread can.
/// So the number of effective steps of any schedule is at most the initial
/// measure (`effective_le`).
///
/// The fix-up is the one step that raises a part of the measure: it moves
/// every worker from Stopped (weight 0) to Loop (2).  It also pushes at
/// least one object, white or grey and off every stack before, which costs
/// 2 nr + 3 + 9f and costs 2 + 9f after; so it lowers the measure by at
/// least 1 too.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.Term

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

module HeapGraph = GC.Spec.HeapGraph
module M1 = GC.Spec.MarkPar.Model
module I1 = GC.Spec.MarkPar.Inv
module Own = GC.Spec.MarkPar.Own
module LS = GC.Spec.MarkPar2.Lists
module U = GC.Spec.MarkPar2.Upd
module St = GC.Spec.MarkPar2.Step
module FX = GC.Spec.MarkPar2.Fix
module Mn = GC.Spec.MarkPar2.Main
module E = GC.Spec.MarkPar2.End
module W = GC.Spec.MarkPar2.Weight
module Ms = GC.Spec.MarkPar2.Meas

/// ---------------------------------------------------------------------------
/// Enabled events
/// ---------------------------------------------------------------------------

let rec mem_worker_events (s: state) (j: nat) (ws: list wk) (e: event)
  : Lemma (ensures L.mem e (worker_events s j ws) <==>
                   (match e with
                    | W i -> i >= j /\ (match M1.nth ws (i - j) with Some w -> wk_enabled s w | None -> false)
                    | Main -> false))
          (decreases ws)
  = match ws with
    | [] -> ()
    | w :: rest ->
      L.append_mem (if wk_enabled s w then [W j] else []) (worker_events s (j + 1) rest) e;
      mem_worker_events s (j + 1) rest e

let mem_enabled (s: state) (e: event)
  : Lemma (L.mem e (enabled s) <==>
           ~s.finished /\
           (match e with
            | W i -> (match M1.nth s.wks i with Some w -> wk_enabled s w | None -> false)
            | Main -> all_stopped s.wks))
  = if s.finished then ()
    else begin
      L.append_mem (worker_events s 0 s.wks) (if all_stopped s.wks then [Main] else []) e;
      mem_worker_events s 0 s.wks e
    end

let rec set_set (#a: Type) (l: list a) (i: nat) (x y: a)
  : Lemma (ensures M1.set_nth (M1.set_nth l i x) i y == M1.set_nth l i y) (decreases l)
  = match l with [] -> () | _ :: r -> if i = 0 then () else set_set r (i - 1) x y

let rec set_same (#a: Type) (l: list a) (i: nat) (x: a)
  : Lemma (requires M1.nth l i == Some x) (ensures M1.set_nth l i x == l) (decreases l)
  = match l with [] -> () | _ :: r -> if i = 0 then () else set_same r (i - 1) x

/// A spin step keeps the measure, and the worker's next step undoes it.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let spin_same (k: cfg) (s: state) (i: nat) (w: wk) (p: pc)
  : Lemma (requires M1.nth s.wks i == Some w /\ w.stack == [] /\ w.inbox == [] /\ s.count > 0 /\
                    (w.pc == Loop /\ p == Idle \/ w.pc == Idle /\ p == Loop))
          (ensures (let w' = { w with pc = p } in
                    let s' = { s with wks = M1.set_nth s.wks i w' } in
                    let w'' = { w' with pc = w.pc } in
                    measure k s' == measure k s /\
                    M1.nth s'.wks i == Some w' /\
                    ({ s' with wks = M1.set_nth s'.wks i w'' }) == s))
  = let w' = { w with pc = p } in
    let s' = { s with wks = M1.set_nth s.wks i w' } in
    Own.nth_lt s.wks i;
    Ms.set_same_stacks s.wks i w';
    Ms.om_same k s.heap s s';
    W.wks_w_set k s.heap s.count s.wks i w';
    Own.nth_set_nth s.wks i i w';
    set_set s.wks i w' w;
    assert ({ w' with pc = w.pc } == w);
    set_same s.wks i w
#pop-options

let disabled_spin (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (e: event)
  : Lemma (requires inv k g roots s /\ ~(L.mem e (enabled s)))
          (ensures step k s e == s \/
                   (spin s e /\ measure k (step k s e) == measure k s /\
                    step k (step k s e) e == s))
  = mem_enabled s e;
    match e with
    | Main -> ()
    | W i ->
      if s.finished then ()
      else match M1.nth s.wks i with
        | None -> ()
        | Some w ->
          match w.pc with
          | Loop -> if Nil? w.stack && Nil? w.inbox then spin_same k s i w Idle
          | Idle ->
            reveal_opaque (`%own_ok) (own_ok k g s);
            assert (wk_of s i == Some w);
            assert (wk_ok k g s.heap i w);
            spin_same k s i w Loop
          | _ -> ()

/// Some record has something counted.
let rec counted_some (ws: list wk)
  : Lemma (requires counted ws > 0)
          (ensures exists (i: nat) (w: wk). M1.nth ws i == Some w /\ LS.size w > 0)
          (decreases ws)
  = match ws with
    | [] -> ()
    | w :: rest ->
      if LS.size w > 0 then assert (M1.nth ws 0 == Some w)
      else begin
        counted_some rest;
        let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
                  (fun i -> exists (w': wk). M1.nth rest i == Some w' /\ LS.size w' > 0) in
        assert (exists (w': wk). M1.nth ws (i + 1) == Some w' /\ LS.size w' > 0)
      end

/// A worker with something counted, in a running state, can move.
let busy_enabled (k: cfg) (g: heap) (s: state) (i: nat) (w: wk)
  : Lemma (requires count_ok s /\ own_ok k g s /\ wk_of s i == Some w /\ LS.size w > 0)
          (ensures wk_enabled s w)
  = reveal_opaque (`%count_ok) (count_ok s);
    reveal_opaque (`%own_ok) (own_ok k g s);
    assert (wk_ok k g s.heap i w);
    LS.counted_ge s.wks i

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let enabled_nil (k: cfg) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires inv k g roots s) (ensures enabled s == [] <==> s.finished)
  = if s.finished then ()
    else if all_stopped s.wks then mem_enabled s Main
    else begin
      reveal_opaque (`%count_ok) (count_ok s);
      // Some worker has not stopped.
      let ns () : Lemma (exists (i: nat) (w: wk). M1.nth s.wks i == Some w /\ ~(Stopped? w.pc)) =
        FStar.Classical.move_requires LS.all_stopped_intro s.wks in
      ns ();
      let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun i -> exists (w: wk). M1.nth s.wks i == Some w /\ ~(Stopped? w.pc)) in
      let Some w = M1.nth s.wks i in
      if wk_enabled s w then mem_enabled s (W i)
      else begin
        // w is at Loop or Idle with nothing, and the counter is not 0.
        assert (s.count > 0);
        counted_some s.wks;
        let j = FStar.IndefiniteDescription.indefinite_description_ghost nat
                  (fun j -> exists (w': wk). M1.nth s.wks j == Some w' /\ LS.size w' > 0) in
        let Some w' = M1.nth s.wks j in
        busy_enabled k g s j w';
        mem_enabled s (W j)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Worker steps lower the measure
/// ---------------------------------------------------------------------------

let mpre (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk) : prop =
  St.step_pre k g roots s i w

let measure_of (k: cfg) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires inv k g roots s)
          (ensures measure k s == Ms.om k g s + Ms.wm k g s + (if s.finished then 0 else 1))
  = U.own_heap k g s;
    Ms.measure_parts k g s

/// A record replaced without touching the stack: om unchanged.
let om_rec (k: cfg) (g: heap) (s: state) (i: nat) (w w': wk) (n: nat)
  : Lemma (requires M1.nth s.wks i == Some w /\ w'.stack == w.stack)
          (ensures Ms.om k g (U.upd s i w' s.heap n) == Ms.om k g s)
  = Ms.set_same_stacks s.wks i w';
    Ms.om_same k g s (U.upd s i w' s.heap n)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let drop_rec (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w w': wk) (n: nat)
  : Lemma (requires mpre k g roots s i w /\ w'.stack == w.stack /\
                    W.wkw k g s.count w' + 1 <= W.wkw k g s.count w /\
                    (n > 0 ==> s.count > 0) /\
                    inv k g roots (U.upd s i w' s.heap n))
          (ensures measure k (U.upd s i w' s.heap n) < measure k s)
  = let s' = U.upd s i w' s.heap n in
    measure_of k g roots s;
    measure_of k g roots s';
    om_rec k g s i w w' n;
    W.wks_w_set k g s.count s.wks i w';
    W.wks_w_count k g n s.count s'.wks
#pop-options

/// Pop: x's weight, 2 + 9f, goes; the program counter gains 9f + 1.
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let drop_pop (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk)
    (x: obj_addr) (rest: list obj_addr)
  : Lemma (requires mpre k g roots s i w /\ w.pc == Loop /\ w.stack == x :: rest)
          (ensures measure k (wstep k s i) < measure k s)
  = let h' = makeBlack_x x s.heap in
    St.pop_record k g s i w x rest;
    St.pop_heap k g s x;
    St.step_pop k g roots s i w x rest;
    U.own_heap k g s;
    let w' = { w with stack = rest; pc = St.pop_pc s x } in
    let s' = U.upd s i w' h' s.count in
    assert (wstep k s i == s');
    measure_of k g roots s;
    measure_of k g roots s';
    W.wks_w_set k g s.count s.wks i w';
    LS.objs_list_mem g x;
    W.fields_rec g s.heap x;
    W.fields_rec g h' x;
    colors x s.heap; colors x h';
    Own.nth_lt s.wks i;
    Own.nth_set_nth s.wks i i w';
    let aux (y: obj_addr) : Lemma (requires L.memP y (objs_list g))
        (ensures obj_w k h' s'.wks y <= obj_w k s.heap s.wks y) =
      LS.objs_list_mem g y;
      W.fields_rec g s.heap y; W.fields_rec g h' y;
      if y = x then ()
      else begin
        Own.nth_set_nth s.wks i (own k y) w';
        L.mem_memP y (x :: rest); L.mem_memP y rest
      end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    W.objs_w_drop k s.heap h' s.wks s'.wks (objs_list g) x (2 + 9 * M1.fields_to_scan x s.heap)
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let drop_take (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk)
    (v: obj_addr) (rest: list obj_addr)
  : Lemma (requires mpre k g roots s i w /\ w.pc == Loop /\ w.stack == [] /\ w.inbox == v :: rest)
          (ensures measure k (wstep k s i) < measure k s)
  = let w' = { w with inbox = rest; pc = Got v } in
    St.step_take k g roots s i w v rest;
    assert (wstep k s i == U.upd s i w' s.heap s.count);
    drop_rec k g roots s i w w' s.count
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let drop_empty (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk)
  : Lemma (requires mpre k g roots s i w /\ w.pc == Loop /\ w.stack == [] /\ w.inbox == [] /\ s.count == 0)
          (ensures measure k (wstep k s i) < measure k s)
  = let w' = { w with pc = Idle } in
    St.step_empty k g roots s i w;
    assert (wstep k s i == U.upd s i w' s.heap s.count);
    drop_rec k g roots s i w w' s.count
#pop-options

/// Idle, with the counter at 0 or a message waiting.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let drop_idle (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk)
  : Lemma (requires mpre k g roots s i w /\ w.pc == Idle /\ (s.count == 0 \/ Cons? w.inbox))
          (ensures measure k (wstep k s i) < measure k s)
  = let w' = { w with pc = if s.count = 0 then Stopped else Loop } in
    St.step_idle k g roots s i w;
    assert (wstep k s i == U.upd s i w' s.heap s.count);
    drop_rec k g roots s i w w' s.count
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let drop_finish (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk)
  : Lemma (requires mpre k g roots s i w /\ w.pc == Finish)
          (ensures measure k (wstep k s i) < measure k s)
  = let w' = { w with pc = Loop } in
    St.step_finish k g roots s i w;
    U.own_rec k g s i w;
    U.count_pos s i;
    let n : nat = s.count - 1 in
    assert (wstep k s i == U.upd s i w' s.heap n);
    drop_rec k g roots s i w w' n
#pop-options

/// The middle state of a scan or an accept: the program counter moved on.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let mid_parts (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk) (p: pc)
  : Lemma (requires mpre k g roots s i w)
          (ensures (let s0 = U.upd s i { w with pc = p } s.heap s.count in
                    Ms.om k g s0 == Ms.om k g s /\
                    Ms.wm k g s0 + W.wkw k g s.count w == Ms.wm k g s + W.wkw k g s.count { w with pc = p } /\
                    recoloured g s0.heap /\ L.length s0.wks == nr k /\ i < L.length s0.wks))
  = let w' = { w with pc = p } in
    om_rec k g s i w w' s.count;
    W.wks_w_set k g s.count s.wks i w';
    U.own_heap k g s;
    Own.length_set_nth s.wks i w'
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let drop_scan (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk) (sc: M1.scanning)
  : Lemma (requires mpre k g roots s i w /\ w.pc == Scan sc)
          (ensures measure k (wstep k s i) < measure k s)
  = let p = St.next_pc sc in
    let s0 = U.upd s i { w with pc = p } s.heap s.count in
    St.step_scan k g roots s i w sc;
    St.scan_field k g s i w sc;
    U.own_rec k g s i w;
    U.count_pos s i;
    mid_parts k g roots s i w p;
    measure_of k g roots s;
    measure_of k g roots (wstep k s i);
    ctx_elim k g roots;
    let v = get_field_x s.heap sc.M1.sobj sc.M1.snext in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      St.scan_target k g roots s sc.M1.sobj sc.M1.snext;
      Ms.route_m k g s0 i v;
      assert (wstep k s i == route k s0 i v)
    end else assert (wstep k s i == s0)
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let drop_got (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat) (w: wk) (v: obj_addr)
  : Lemma (requires mpre k g roots s i w /\ w.pc == Got v)
          (ensures measure k (wstep k s i) < measure k s)
  = let s0 = U.upd s i { w with pc = Finish } s.heap s.count in
    St.step_got k g roots s i w v;
    U.own_rec k g s i w;
    U.count_pos s i;
    mid_parts k g roots s i w Finish;
    measure_of k g roots s;
    measure_of k g roots (wstep k s i);
    ctx_elim k g roots;
    Ms.accept_m k g s0 i v;
    assert (wstep k s i == accept k s0 i v)
#pop-options

let wstep_drops (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (i: nat)
  : Lemma (requires ctx k g roots /\ inv k g roots s /\ ~s.finished /\ L.mem (W i) (enabled s))
          (ensures measure k (wstep k s i) < measure k s)
  = mem_enabled s (W i);
    U.own_len k g s;
    Own.nth_lt s.wks i;
    U.old_eq s i;
    let w = U.old s i in
    match w.pc with
    | Loop ->
      (match w.stack with
       | x :: rest -> drop_pop k g roots s i w x rest
       | [] ->
         (match w.inbox with
          | v :: rest -> drop_take k g roots s i w v rest
          | [] -> drop_empty k g roots s i w))
    | Idle -> drop_idle k g roots s i w
    | Scan sc -> drop_scan k g roots s i w sc
    | Got v -> drop_got k g roots s i w v
    | Finish -> drop_finish k g roots s i w

/// ---------------------------------------------------------------------------
/// The main step lowers the measure
/// ---------------------------------------------------------------------------

let main_done_drops (k: cfg) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires inv k g roots s /\ ~s.finished /\ ~(flagged s))
          (ensures measure k (main_step k s) < measure k s)
  = U.own_heap k g s;
    Ms.measure_parts k g s;
    Ms.measure_parts k g (main_step k s)

/// Nothing is on a stack when every stack is empty.
let empty_off (k: cfg) (s: state) (x: obj_addr)
  : Lemma (requires forall (i: nat) (w: wk). wk_of s i == Some w ==> w.stack == [])
          (ensures ~(on_stack k s.wks x))
  = match M1.nth s.wks (own k x) with Some w -> assert (wk_of s (own k x) == Some w) | None -> ()

/// One object's weight across the walk.
let x_weight (k: cfg) (h1 h2: heap) (ws1 ws2: list wk) (x: obj_addr)
  : Lemma (requires ~(on_stack k ws1 x) /\ M1.fields_to_scan x h1 == M1.fields_to_scan x h2 /\
                    (~(is_white x h1) ==> ~(is_white x h2)) /\ (is_black x h2 <==> is_black x h1) /\
                    (is_gray x h1 ==> is_gray x h2) /\ (is_blue x h1 <==> is_blue x h2))
          (ensures obj_w k h2 ws2 x <= obj_w k h1 ws1 x /\
                   (on_stack k ws2 x /\ is_gray x h2 ==> obj_w k h2 ws2 x + 2 * nr k + 1 <= obj_w k h1 ws1 x))
  = colors x h1; colors x h2

/// The walk only greys, and only adds to stacks that start empty: no object
/// gains weight, and an object on a stack at the end lost 2 nr + 1.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let walk_weights (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (f: fx) (ws': list wk)
  : Lemma (requires inv k g roots s /\ all_stopped s.wks /\ FX.grows (Mn.start_fx s) f /\
                    FX.wbase k g roots f /\ Ms.same_stacks f.fws ws')
          (ensures (forall (x: obj_addr). L.memP x (objs_list g) ==>
                      obj_w k f.fh ws' x <= obj_w k s.heap s.wks x) /\
                   (forall (x: obj_addr). L.memP x (objs_list g) /\ on_stack k ws' x /\ is_gray x f.fh ==>
                      obj_w k f.fh ws' x + 2 * nr k + 1 <= obj_w k s.heap s.wks x))
  = Mn.stopped_empty k g s;
    U.own_heap k g s;
    FX.wbase_heap k g roots f;
    let aux (x: obj_addr) : Lemma (requires L.memP x (objs_list g))
        (ensures obj_w k f.fh ws' x <= obj_w k s.heap s.wks x /\
                 (on_stack k ws' x /\ is_gray x f.fh ==> obj_w k f.fh ws' x + 2 * nr k + 1 <= obj_w k s.heap s.wks x)) =
      LS.objs_list_mem g x;
      W.fields_rec g s.heap x; W.fields_rec g f.fh x;
      recoloured_blue g s.heap x; recoloured_blue g f.fh x;
      empty_off k s x;
      x_weight k s.heap f.fh s.wks ws' x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// A positive count after the walk names an object on a stack.
let some_pushed (k: cfg) (g: heap) (roots: list obj_addr) (f: fx)
  : Lemma (requires FX.wbase k g roots f /\ f.fn > 0)
          (ensures exists (x: obj_addr). L.memP x (objs_list g) /\ on_stack k f.fws x /\ is_gray x f.fh)
  = reveal_opaque (`%FX.wbase) (FX.wbase k g roots f);
    counted_some f.fws;
    let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun i -> exists (w: wk). M1.nth f.fws i == Some w /\ LS.size w > 0) in
    let Some w = M1.nth f.fws i in
    assert (FX.fwk f i == Some w);
    assert (FX.wrec_ok k g f.fh i w);
    let x :: _ = w.stack in
    LS.objs_list_mem g x;
    assert (own k x == i)

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let main_fix_drops (k: cfg) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires ctx k g roots /\ inv k g roots s /\ ~s.finished /\ all_stopped s.wks /\ flagged s)
          (ensures measure k (main_step k s) < measure k s)
  = let f0 = Mn.start_fx s in
    Mn.walk_start k g roots s;
    FX.walk_step k g roots f0 (objs_list s.heap) (U64.v zero_addr);
    let f = fix_walk k f0 (objs_list s.heap) in
    U.own_heap k g s;
    Mn.stopped_empty k g s;
    introduce forall (i: nat) (w: wk). M1.nth s.wks i == Some w ==> w.inbox == [] /\ w.pc == Stopped
    with introduce _ ==> _ with Mn.stopped_at k g s i w;
    W.wks_w_stopped k g s.count s.wks;
    Ms.measure_parts k g s;
    reveal_opaque (`%FX.wbase) (FX.wbase k g roots f);
    Mn.like_walk k g roots f;
    if f.fn = 0 then begin
      let s' = { s with heap = f.fh; wks = f.fws; ovf_main = f.fom; finished = true } in
      assert (main_step k s == s');
      Ms.measure_parts k g s';
      introduce forall (i: nat) (w: wk). M1.nth f.fws i == Some w ==> w.inbox == [] /\ w.pc == Stopped
      with introduce _ ==> _ with FX.wbase_at k g roots f i w;
      W.wks_w_stopped k g s.count f.fws;
      assert (Ms.same_stacks f.fws f.fws);
      walk_weights k g roots s f f.fws;
      W.objs_w_mono k s.heap f.fh s.wks f.fws (objs_list g)
    end else begin
      let ws' = restart f.fws in
      let s' = { s with heap = f.fh; wks = ws'; count = f.fn; ovf_main = f.fom } in
      assert (main_step k s == s');
      Ms.measure_parts k g s';
      introduce forall (i: nat) (w: wk). M1.nth f.fws i == Some w ==> w.inbox == []
      with introduce _ ==> _ with Mn.like_at k g f f.fws i w;
      W.wks_w_restart k g f.fn f.fws;
      LS.length_restart f.fws;
      FStar.Classical.forall_intro (LS.nth_restart f.fws);
      assert (Ms.same_stacks f.fws ws');
      walk_weights k g roots s f ws';
      some_pushed k g roots f;
      let c = FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
                (fun x -> L.memP x (objs_list g) /\ on_stack k f.fws x /\ is_gray x f.fh) in
      Ms.on_stack_same k f.fws ws' c;
      W.objs_w_drop k s.heap f.fh s.wks ws' (objs_list g) c (2 * nr k + 1)
    end
#pop-options

let main_drops (k: cfg) (g: heap) (roots: list obj_addr) (s: state)
  : Lemma (requires ctx k g roots /\ inv k g roots s /\ ~s.finished /\ all_stopped s.wks)
          (ensures measure k (main_step k s) < measure k s)
  = if flagged s then main_fix_drops k g roots s else main_done_drops k g roots s

/// ---------------------------------------------------------------------------
/// Every run ends
/// ---------------------------------------------------------------------------

let enabled_drops (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (e: event)
  : Lemma (requires ctx k g roots /\ inv k g roots s /\ L.mem e (enabled s))
          (ensures measure k (step k s e) < measure k s)
  = mem_enabled s e;
    match e with
    | W i -> wstep_drops k g roots s i
    | Main -> main_drops k g roots s

let rec effective_le (k: cfg) (g: heap) (roots: list obj_addr) (s: state) (sched: list event)
  : Lemma (requires ctx k g roots /\ inv k g roots s)
          (ensures effective_steps k s sched <= measure k s)
          (decreases sched)
  = match sched with
    | [] -> ()
    | e :: rest ->
      E.step_inv k g roots s e;
      effective_le k g roots (step k s e) rest;
      if L.mem e (enabled s) then enabled_drops k g roots s e
      else disabled_spin k g roots s e
