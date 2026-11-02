/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Term — the Stage 1 model's runs end
///
/// The proof of `GC.Spec.MarkPar.mark_par_terminates`, which Stage 2 left
/// admitted.  From any state a run reaches (`Own.inv_own`):
///   * an enabled event lowers `measure` by at least 1 (`enabled_drops`):
///       Pop      an entry's 1 + 3f becomes the scan's 3f
///       Scan     the field's 3 goes; greying a white object owned here
///                turns its 2 + 3f into a work entry's 1 + 3f; a message
///                adds 2
///       Take     the entry's 1 goes; greying turns 2 + 3f into 1 + 3f
///       Deliver  the message's 2 becomes an inbox entry's 1
///   * an event that is not enabled changes nothing (`disabled_same`);
///   * nothing is enabled exactly when the run is quiescent (`enabled_nil`).
/// The weights do not depend on colours, only on the heap's layout, which
/// recolouring keeps.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar.Term

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
open GC.Spec.MarkPar.Model
open GC.Spec.MarkPar.Recolour

module HeapGraph = GC.Spec.HeapGraph
module Own = GC.Spec.MarkPar.Own
module I = GC.Spec.MarkPar.Inv
module SP = FStar.Seq.Properties

let objs (g: heap) = objects zero_addr g
let olist (h: heap) : list obj_addr = Seq.seq_to_list (objects_x zero_addr h)

/// ---------------------------------------------------------------------------
/// Weights do not depend on colours
/// ---------------------------------------------------------------------------

let fts_rec (g h: heap) (x: obj_addr)
  : Lemma (requires recoloured g h /\ Seq.mem x (objs g))
          (ensures fields_to_scan x h == fields_to_scan x g)
  = recoloured_wosize g h x; recoloured_no_scan g h x

let rec work_weight_rec (g h: heap) (l: list obj_addr)
  : Lemma (requires recoloured g h /\ (forall (x: obj_addr). L.memP x l ==> Seq.mem x (objs g)))
          (ensures work_weight h l == work_weight g l) (decreases l)
  = match l with [] -> () | x :: r -> fts_rec g h x; work_weight_rec g h r

/// Every work list of ws holds enumerated objects.
let rec works_in (g: heap) (ws: list worker) : Tot prop (decreases ws) =
  match ws with
  | [] -> True
  | w :: r -> (forall (x: obj_addr). L.memP x w.work ==> Seq.mem x (objs g)) /\ works_in g r

let rec works_in_intro (g: heap) (ws: list worker)
  : Lemma (requires forall (i: nat). match nth ws i with
                                | Some w -> (forall (x: obj_addr). L.memP x w.work ==> Seq.mem x (objs g))
                                | None -> True)
          (ensures works_in g ws) (decreases ws)
  = match ws with
    | [] -> ()
    | w :: r ->
      assert (nth ws 0 == Some w);
      let aux (i: nat) : Lemma (match nth r i with
                                | Some w -> (forall (x: obj_addr). L.memP x w.work ==> Seq.mem x (objs g))
                                | None -> True) =
        assert (nth ws (i + 1) == nth r i) in
      FStar.Classical.forall_intro aux;
      works_in_intro g r

let rec workers_weight_rec (g h: heap) (ws: list worker)
  : Lemma (requires recoloured g h /\ works_in g ws)
          (ensures workers_weight h ws == workers_weight g ws) (decreases ws)
  = match ws with [] -> () | w :: r -> work_weight_rec g h w.work; workers_weight_rec g h r

let inv_works (cs: list nat) (g: heap) (s: state)
  : Lemma (requires Own.inv_own cs g s) (ensures works_in g s.workers /\ recoloured g s.heap)
  = let aux (i: nat) : Lemma (match nth s.workers i with
                              | Some w -> (forall (x: obj_addr). L.memP x w.work ==> Seq.mem x (objs g))
                              | None -> True) =
      match nth s.workers i with
      | Some w -> assert (Own.worker_ok cs g s.heap i w)
      | None -> ()
    in
    FStar.Classical.forall_intro aux;
    works_in_intro g s.workers

/// ---------------------------------------------------------------------------
/// One worker's weight
/// ---------------------------------------------------------------------------

let ww (g: heap) (w: worker) : nat = work_weight g w.work + scan_weight w.scan + L.length w.inbox

let rec workers_weight_set (g: heap) (ws: list worker) (i: nat) (w: worker)
  : Lemma (ensures (match nth ws i with
                    | Some w0 -> workers_weight g (set_nth ws i w) + ww g w0 == workers_weight g ws + ww g w
                    | None -> workers_weight g (set_nth ws i w) == workers_weight g ws))
          (decreases ws)
  = match ws with [] -> () | _ :: r -> if i = 0 then () else workers_weight_set g r (i - 1) w

/// ---------------------------------------------------------------------------
/// The objects' weight
/// ---------------------------------------------------------------------------

let wt (h: heap) (y: obj_addr) : nat = if is_white_x y h then 2 + 3 * fields_to_scan y h else 0

let rec white_mono (h1 h2: heap) (l: list obj_addr)
  : Lemma (requires forall (y: obj_addr). L.memP y l ==> wt h2 y <= wt h1 y)
          (ensures white_weight h2 l <= white_weight h1 l) (decreases l)
  = match l with [] -> () | _ :: r -> white_mono h1 h2 r

let rec white_drop (h1 h2: heap) (l: list obj_addr) (c: obj_addr) (d: nat)
  : Lemma (requires (forall (y: obj_addr). L.memP y l ==> wt h2 y <= wt h1 y) /\
                    L.memP c l /\ wt h2 c + d <= wt h1 c)
          (ensures white_weight h2 l + d <= white_weight h1 l) (decreases l)
  = match l with
    | [] -> ()
    | y :: r -> if y = c then white_mono h1 h2 r else white_drop h1 h2 r c d

/// Recolouring x keeps every other object's weight.
let wt_other (g h: heap) (x y: obj_addr) (c: color)
  : Lemma (requires recoloured g h /\ recoloured g (set_object_color x h c) /\
                    Seq.mem y (objs g) /\ y <> x)
          (ensures wt (set_object_color x h c) y == wt h y)
  = Own.other_color h x y c;
    fts_rec g h y; fts_rec g (set_object_color x h c) y

let measure_parts (g: heap) (s: state)
  : Lemma (requires recoloured g s.heap /\ works_in g s.workers)
          (ensures measure s == white_weight s.heap (olist g) + workers_weight g s.workers +
                                2 * L.length s.net)
  = workers_weight_rec g s.heap s.workers

let olist_mem (g: heap) (x: obj_addr)
  : Lemma (L.memP x (olist g) <==> Seq.mem x (objs g))
  = SP.lemma_seq_to_list_permutation (objects_x zero_addr g);
    L.mem_memP x (olist g);
    L.mem_count (olist g) x

/// ---------------------------------------------------------------------------
/// The steps
/// ---------------------------------------------------------------------------

let tpre (cs: list nat) (g: heap) (roots: list obj_addr) (s: state) : prop =
  I.ctx cs g roots /\ Own.inv_own cs g s

/// A colour change that keeps every object's weight, or lowers it.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let white_after (g h h': heap) (x: obj_addr) (c: color)
  : Lemma (requires recoloured g h /\ h' == set_object_color x h c /\ recoloured g h' /\
                    ~(is_white x h') /\ Seq.mem x (objs g))
          (ensures white_weight h' (olist g) + wt h x <= white_weight h (olist g) + wt h' x /\
                   wt h' x == 0)
  = I.colors x h';
    let aux (y: obj_addr) : Lemma (requires L.memP y (olist g)) (ensures wt h' y <= wt h y) =
      olist_mem g y;
      if y = x then () else wt_other g h x y c
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    olist_mem g x;
    if is_white_x x h then white_drop h h' (olist g) x (wt h x)
    else white_mono h h' (olist g)
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let drop_pop (cs: list nat) (g: heap) (roots: list obj_addr) (s: state) (i: nat)
    (w: worker) (x: obj_addr) (rest: list obj_addr)
  : Lemma (requires tpre cs g roots s /\ nth s.workers i == Some w /\ w.scan == None /\ w.work == x :: rest)
          (ensures measure (step cs s (Pop i)) < measure s)
  = let s' = step cs s (Pop i) in
    let w' = Own.pop_worker s w x rest in
    Own.nth_lt s.workers i;
    assert (Own.worker_ok cs g s.heap i w);
    assert (s' == { s with heap = makeBlack_x x s.heap; workers = set_nth s.workers i w' });
    Own.step_own cs g s (Pop i);
    inv_works cs g s; inv_works cs g s';
    measure_parts g s; measure_parts g s';
    makeBlack_eq x s.heap; makeBlack_is_black x s.heap;
    I.colors x s'.heap;
    white_after g s.heap s'.heap x Black;
    I.colors x s.heap;
    workers_weight_set g s.workers i w';
    fts_rec g s.heap x;
    recoloured_wosize g s.heap x; recoloured_no_scan g s.heap x
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let drop_take (cs: list nat) (g: heap) (roots: list obj_addr) (s: state) (i: nat)
    (w: worker) (x: obj_addr) (rest: list obj_addr)
  : Lemma (requires tpre cs g roots s /\ nth s.workers i == Some w /\ w.inbox == x :: rest)
          (ensures measure (step cs s (Take i)) < measure s)
  = let s' = step cs s (Take i) in
    Own.nth_lt s.workers i;
    assert (Own.worker_ok cs g s.heap i w);
    assert (Own.entry_ok cs g i x);
    Own.step_own cs g s (Take i);
    inv_works cs g s; inv_works cs g s';
    measure_parts g s; measure_parts g s';
    let w0 = { w with inbox = rest } in
    if is_white_x x s.heap then begin
      let w' = { w0 with work = x :: w0.work } in
      assert (s' == { s with heap = makeGray_x x s.heap; workers = set_nth s.workers i w' });
      makeGray_eq x s.heap; makeGray_is_gray x s.heap;
      I.colors x s'.heap;
      white_after g s.heap s'.heap x Gray;
      workers_weight_set g s.workers i w';
      fts_rec g s.heap x
    end else begin
      assert (s' == { s with workers = set_nth s.workers i w0 });
      workers_weight_set g s.workers i w0
    end
#pop-options

let rec length_remove_nth (#a: Type) (l: list a) (j: nat)
  : Lemma (requires j < L.length l) (ensures L.length (remove_nth l j) == L.length l - 1) (decreases l)
  = match l with _ :: r -> if j = 0 then () else length_remove_nth r (j - 1)

#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let drop_deliver (cs: list nat) (g: heap) (roots: list obj_addr) (s: state) (j: nat)
    (m: msg) (w: worker)
  : Lemma (requires tpre cs g roots s /\ nth s.net j == Some m /\ nth s.workers m.dest == Some w)
          (ensures measure (step cs s (Deliver j)) < measure s)
  = let s' = step cs s (Deliver j) in
    let w' = { w with inbox = w.inbox @ [m.addr] } in
    assert (s' == { s with workers = set_nth s.workers m.dest w'; net = remove_nth s.net j });
    Own.step_own cs g s (Deliver j);
    inv_works cs g s; inv_works cs g s';
    measure_parts g s; measure_parts g s';
    workers_weight_set g s.workers m.dest w';
    L.append_length w.inbox [m.addr];
    assert (ww g w' == ww g w + 1);
    Own.nth_lt s.net j;
    length_remove_nth s.net j;
    assert (s'.heap == s.heap);
    assert (L.length s'.net + 1 == L.length s.net);
    assert (workers_weight g s'.workers == workers_weight g s.workers + 1)
#pop-options

#push-options "--fuel 2"
let len1 (#a: Type) (x: a) : Lemma (L.length [x] == 1) = ()
#pop-options

/// A scan step, by its outcome (`I.scan_rel`).
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let drop_scan (cs: list nat) (g: heap) (roots: list obj_addr) (s: state) (i: nat)
    (w: worker) (sc: scanning)
  : Lemma (requires tpre cs g roots s /\ nth s.workers i == Some w /\ w.scan == Some sc)
          (ensures measure (step cs s (Scan i)) < measure s)
  = let s' = step cs s (Scan i) in
    Own.nth_lt s.workers i;
    assert (Own.worker_ok cs g s.heap i w);
    Own.step_own cs g s (Scan i);
    inv_works cs g s; inv_works cs g s';
    measure_parts g s; measure_parts g s';
    I.scan_x cs g s i sc;
    let x = sc.sobj in
    let w0 = { w with scan = next_field sc } in
    assert (scan_weight (next_field sc) + 3 == scan_weight (Some sc));
    let v = get_field_x s.heap x sc.snext in
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let c = resolve_x v s.heap in
      let o = owner cs c in
      assert (v == HeapGraph.get_field g x sc.snext);
      assert (I.is_field g x sc.snext);
      I.target_facts cs g roots x sc.snext;
      assert (c == I.field_target g x sc.snext);
      if o = i then begin
        if is_white_x c s.heap then begin
          let w' = { w0 with work = c :: w0.work } in
          assert (s' == { s with heap = makeGray_x c s.heap; workers = set_nth s.workers i w' });
          makeGray_eq c s.heap; makeGray_is_gray c s.heap;
          I.colors c s'.heap;
          white_after g s.heap s'.heap c Gray;
          workers_weight_set g s.workers i w';
          fts_rec g s.heap c
        end else begin
          assert (s' == { s with workers = set_nth s.workers i w0 });
          workers_weight_set g s.workers i w0
        end
      end else begin
        assert (s' == { s with workers = set_nth s.workers i w0; net = s.net @ [{ dest = o; addr = c }] });
        workers_weight_set g s.workers i w0;
        L.append_length s.net [{ dest = o; addr = c }];
        len1 ({ dest = o; addr = c })
      end
    end else begin
      assert (s' == { s with workers = set_nth s.workers i w0 });
      workers_weight_set g s.workers i w0
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Enabled events
/// ---------------------------------------------------------------------------

let rec mem_worker_events (i: nat) (ws: list worker) (e: event)
  : Lemma (ensures L.mem e (worker_events i ws) <==>
                   (match e with
                    | Pop j -> j >= i /\ (match nth ws (j - i) with
                                         | Some w -> None? w.scan && Cons? w.work | None -> false)
                    | Scan j -> j >= i /\ (match nth ws (j - i) with Some w -> Some? w.scan | None -> false)
                    | Take j -> j >= i /\ (match nth ws (j - i) with Some w -> Cons? w.inbox | None -> false)
                    | Deliver _ -> false))
          (decreases ws)
  = match ws with
    | [] -> ()
    | w :: rest ->
      let here = (if Some? w.scan then [Scan i] else if Cons? w.work then [Pop i] else [])
                 @ (if Cons? w.inbox then [Take i] else []) in
      L.append_mem here (worker_events (i + 1) rest) e;
      L.append_mem (if Some? w.scan then [Scan i] else if Cons? w.work then [Pop i] else [])
                   (if Cons? w.inbox then [Take i] else []) e;
      mem_worker_events (i + 1) rest e

let rec mem_deliver_events (j: nat) (n: list msg) (e: event)
  : Lemma (ensures L.mem e (deliver_events j n) <==>
                   (match e with Deliver k -> k >= j /\ k - j < L.length n | _ -> false))
          (decreases n)
  = match n with [] -> () | _ :: rest -> mem_deliver_events (j + 1) rest e

let mem_enabled (s: state) (e: event)
  : Lemma (L.mem e (enabled s) <==>
           (match e with
            | Pop i -> (match nth s.workers i with Some w -> None? w.scan && Cons? w.work | None -> false)
            | Scan i -> (match nth s.workers i with Some w -> Some? w.scan | None -> false)
            | Take i -> (match nth s.workers i with Some w -> Cons? w.inbox | None -> false)
            | Deliver j -> j < L.length s.net))
  = L.append_mem (worker_events 0 s.workers) (deliver_events 0 s.net) e;
    mem_worker_events 0 s.workers e;
    mem_deliver_events 0 s.net e

let disabled_same (cs: list nat) (s: state) (e: event)
  : Lemma (requires ~(L.mem e (enabled s))) (ensures step cs s e == s)
  = mem_enabled s e;
    match e with
    | Deliver j -> Own.nth_lt s.net j
    | _ -> ()

let rec worker_events_nil (i: nat) (ws: list worker)
  : Lemma (ensures worker_events i ws == [] <==> L.for_all idle ws) (decreases ws)
  = match ws with
    | [] -> ()
    | w :: rest ->
      L.append_l_nil ((if Some? w.scan then [Scan i] else if Cons? w.work then [Pop i] else [])
                      @ (if Cons? w.inbox then [Take i] else []));
      worker_events_nil (i + 1) rest

let deliver_events_nil (j: nat) (n: list msg)
  : Lemma (ensures deliver_events j n == [] <==> n == [])
  = match n with [] -> () | _ :: _ -> ()

let enabled_nil (s: state) : Lemma (enabled s == [] <==> quiescent s)
  = worker_events_nil 0 s.workers;
    deliver_events_nil 0 s.net;
    L.append_l_nil (worker_events 0 s.workers);
    if Cons? (worker_events 0 s.workers) then () else ()

/// ---------------------------------------------------------------------------
/// Every run ends
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let enabled_drops (cs: list nat) (g: heap) (roots: list obj_addr) (s: state) (e: event)
  : Lemma (requires tpre cs g roots s /\ L.mem e (enabled s))
          (ensures measure (step cs s e) < measure s)
  = mem_enabled s e;
    match e with
    | Pop i -> let Some w = nth s.workers i in let x :: rest = w.work in drop_pop cs g roots s i w x rest
    | Scan i -> let Some w = nth s.workers i in let Some sc = w.scan in drop_scan cs g roots s i w sc
    | Take i -> let Some w = nth s.workers i in let x :: rest = w.inbox in drop_take cs g roots s i w x rest
    | Deliver j ->
      Own.nth_lt s.net j;
      let Some m = nth s.net j in
      Own.nth_memP s.net j m;
      assert (Own.msg_ok cs g m);
      I.count_le_lt cs (U64.v (hd_address m.addr));
      Own.nth_lt s.workers m.dest;
      let Some w = nth s.workers m.dest in
      drop_deliver cs g roots s j m w
#pop-options

let rec effective_le (cs: list nat) (g: heap) (roots: list obj_addr) (s: state) (sched: list event)
  : Lemma (requires tpre cs g roots s)
          (ensures effective_steps cs s sched <= measure s)
          (decreases sched)
  = match sched with
    | [] -> ()
    | e :: rest ->
      Own.step_own cs g s e;
      effective_le cs g roots (step cs s e) rest;
      if L.mem e (enabled s) then enabled_drops cs g roots s e
      else disabled_same cs s e
