/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Own — the ownership invariant, and `step_writes_own`
///
/// In every state a run reaches:
///   * the heap is g recoloured (`GC.Spec.MarkPar.Recolour`);
///   * every work list holds distinct grey objects of its own range;
///   * every inbox entry, and every message's address, is a non-blue object
///     of the range it is for;
///   * a worker part-way through an object owns it, it is black and
///     scannable, and the next field is within its wosize.
/// So the object a step recolours is always one the acting worker owns.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar.Own

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
open GC.Spec.MarkPar.Model
open GC.Spec.MarkPar.Recolour
open GC.Lib.Header

module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module F = GC.Spec.MarkPar.Field

/// ---------------------------------------------------------------------------
/// Lists
/// ---------------------------------------------------------------------------

let rec nth_lt (#a: Type) (l: list a) (i: nat)
  : Lemma (Some? (nth l i) <==> i < L.length l) (decreases l)
  = match l with [] -> () | _ :: r -> if i = 0 then () else nth_lt r (i - 1)

let rec length_set_nth (#a: Type) (l: list a) (i: nat) (v: a)
  : Lemma (L.length (set_nth l i v) == L.length l) (decreases l)
  = match l with [] -> () | _ :: r -> if i = 0 then () else length_set_nth r (i - 1) v

let rec nth_set_nth (#a: Type) (l: list a) (i j: nat) (v: a)
  : Lemma (nth (set_nth l i v) j ==
           (if j = i then (if i < L.length l then Some v else None) else nth l j))
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: r -> if i = 0 || j = 0 then () else nth_set_nth r (i - 1) (j - 1) v

let rec nth_memP (#a: Type) (l: list a) (j: nat) (x: a)
  : Lemma (requires nth l j == Some x) (ensures L.memP x l) (decreases l)
  = match l with [] -> () | _ :: r -> if j = 0 then () else nth_memP r (j - 1) x

let rec memP_remove_nth (#a: Type) (l: list a) (j: nat) (x: a)
  : Lemma (requires L.memP x (remove_nth l j)) (ensures L.memP x l) (decreases l)
  = match l with
    | [] -> ()
    | y :: r -> if j = 0 then () else
        FStar.Classical.or_elim #(x == y) #(L.memP x (remove_nth r (j - 1)))
          #(fun _ -> L.memP x l) (fun _ -> ()) (fun _ -> memP_remove_nth r (j - 1) x)

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

let objs (g: heap) = objects zero_addr g

/// An address worker i may hold in its inbox, or a message to range i.
let entry_ok (cs: list nat) (g: heap) (i: nat) (x: obj_addr) : prop =
  Seq.mem x (objs g) /\ owner cs x == i /\ ~(is_blue x g)

let msg_ok (cs: list nat) (g: heap) (m: msg) : prop = entry_ok cs g m.dest m.addr

let work_rec_ok (cs: list nat) (g h: heap) (i: nat) (l: list obj_addr) : prop =
  L.noRepeats l /\
  (forall (x: obj_addr). L.memP x l ==> Seq.mem x (objs g) /\ owner cs x == i /\ is_gray x h)

let scan_rec_ok (cs: list nat) (g h: heap) (i: nat) (o: option scanning) : prop =
  match o with
  | None -> True
  | Some sc ->
    Seq.mem sc.sobj (objs g) /\ owner cs sc.sobj == i /\ is_black sc.sobj h /\
    ~(is_no_scan sc.sobj g) /\ U64.v sc.snext <= U64.v sc.sws /\
    sc.sws == wosize_of_object sc.sobj g

let worker_ok (cs: list nat) (g h: heap) (i: nat) (w: worker) : prop =
  work_rec_ok cs g h i w.work /\
  (forall (x: obj_addr). L.memP x w.inbox ==> entry_ok cs g i x) /\
  scan_rec_ok cs g h i w.scan

let inv_own (cs: list nat) (g: heap) (s: state) : prop =
  L.length s.workers == nranges cs /\
  recoloured g s.heap /\
  (forall (i: nat) (w: worker). nth s.workers i == Some w ==> worker_ok cs g s.heap i w) /\
  (forall (m: msg). L.memP m s.net ==> msg_ok cs g m)

/// The heap changes only in the header of an object the actor owns.
let writes_own (cs: list nat) (g: heap) (s s': state) (e: event) : prop =
  forall (a: hp_addr). read_word s'.heap a <> read_word s.heap a ==>
    (exists (x: obj_addr). a == hd_address x /\ Seq.mem x (objs g) /\ owner cs x == actor e)

/// ---------------------------------------------------------------------------
/// Colours
/// ---------------------------------------------------------------------------

let other_color (h: heap) (x y: obj_addr) (c: color)
  : Lemma (requires x <> y)
          (ensures is_gray y (set_object_color x h c) == is_gray y h /\
                   is_black y (set_object_color x h c) == is_black y h /\
                   is_white y (set_object_color x h c) == is_white y h)
  = color_change_preserves_other_color x y h c;
    is_gray_iff y h; is_gray_iff y (set_object_color x h c);
    is_black_iff y h; is_black_iff y (set_object_color x h c);
    is_white_iff y h; is_white_iff y (set_object_color x h c)

let colors_distinct (x: obj_addr) (h: heap)
  : Lemma ((is_white x h ==> ~(is_gray x h) /\ ~(is_black x h) /\ ~(is_blue x h)) /\
           (is_gray x h ==> ~(is_black x h) /\ ~(is_blue x h)) /\
           (is_black x h ==> ~(is_blue x h)))
  = is_white_iff x h; is_gray_iff x h; is_black_iff x h; is_blue_iff x h

let set_color_writes (h: heap) (x: obj_addr) (c: color) (a: hp_addr)
  : Lemma (read_word (set_object_color x h c) a <> read_word h a ==> a == hd_address x)
  = if hd_address x <> a then color_change_preserves_other_read x a h c

/// A worker record is unaffected by recolouring an object it does not hold.
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
let worker_ok_other (cs: list nat) (g h: heap) (i: nat) (w: worker) (x: obj_addr) (c: color)
  : Lemma (requires worker_ok cs g h i w /\ ~(L.memP x w.work) /\
                    (match w.scan with Some sc -> sc.sobj <> x | None -> True))
          (ensures worker_ok cs g (set_object_color x h c) i w)
  = let aux (y: obj_addr) : Lemma (requires L.memP y w.work) (ensures is_gray y (set_object_color x h c)) =
      other_color h x y c in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux);
    match w.scan with Some sc -> other_color h x sc.sobj c | None -> ()
#pop-options

let scan_next_ok (cs: list nat) (g h: heap) (i: nat) (sc: scanning)
  : Lemma (requires scan_rec_ok cs g h i (Some sc))
          (ensures scan_rec_ok cs g h i (next_field sc))
  = ()

/// ---------------------------------------------------------------------------
/// Replacing one worker
/// ---------------------------------------------------------------------------

let upd_worker (s: state) (i: nat) (w: worker) (j: nat)
  : Lemma (requires i < L.length s.workers)
          (ensures (let ws = set_nth s.workers i w in
                    L.length ws == L.length s.workers /\
                    nth ws j == (if j = i then Some w else nth s.workers j)))
  = length_set_nth s.workers i w; nth_set_nth s.workers i j w

#push-options "--z3rlimit 30 --fuel 0 --ifuel 0"
let replace_worker (cs: list nat) (g: heap) (s: state) (i: nat) (h': heap) (w': worker) (net': list msg)
  : Lemma (requires L.length s.workers == nranges cs /\ i < L.length s.workers /\
                    recoloured g h' /\ worker_ok cs g h' i w' /\
                    (forall (j: nat) (w: worker). j <> i /\ nth s.workers j == Some w ==>
                       worker_ok cs g h' j w) /\
                    (forall (m: msg). L.memP m net' ==> msg_ok cs g m))
          (ensures inv_own cs g ({ s with heap = h'; workers = set_nth s.workers i w'; net = net' }))
  = FStar.Classical.forall_intro (upd_worker s i w')
#pop-options

/// Workers other than i hold nothing owned by i.
#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
let others_unaffected (cs: list nat) (g: heap) (s: state) (i: nat) (x: obj_addr) (c: color)
  : Lemma (requires inv_own cs g s /\ owner cs x == i)
          (ensures forall (j: nat) (w: worker). j <> i /\ nth s.workers j == Some w ==>
                     worker_ok cs g (set_object_color x s.heap c) j w)
  = let aux (j: nat) (w: worker)
      : Lemma (requires j <> i /\ nth s.workers j == Some w)
              (ensures worker_ok cs g (set_object_color x s.heap c) j w)
      = worker_ok_other cs g s.heap j w x c
    in
    FStar.Classical.forall_intro_2 (fun j w -> FStar.Classical.move_requires (aux j) w)
#pop-options

/// A write at x's header, x owned by the actor, is an owned write.
let writes_at (cs: list nat) (g: heap) (s s': state) (e: event) (x: obj_addr)
  : Lemma (requires Seq.mem x (objs g) /\ owner cs x == actor e /\
                    (forall (a: hp_addr). read_word s'.heap a <> read_word s.heap a ==> a == hd_address x))
          (ensures writes_own cs g s s' e)
  = let aux (a: hp_addr)
      : Lemma (requires read_word s'.heap a <> read_word s.heap a)
              (ensures exists (y: obj_addr). a == hd_address y /\ Seq.mem y (objs g) /\ owner cs y == actor e)
      = FStar.Classical.exists_intro
          (fun (y: obj_addr) -> a == hd_address y /\ Seq.mem y (objs g) /\ owner cs y == actor e) x
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// ---------------------------------------------------------------------------
/// Worker i greys a white object it owns and pushes it
/// ---------------------------------------------------------------------------

/// w0 is worker i's record with its inbox or scan position changed; x is an
/// object i owns.
let push_pre (cs: list nat) (g: heap) (s: state) (i: nat) (w w0: worker) (x: obj_addr) : prop =
  inv_own cs g s /\ nth s.workers i == Some w /\ w0.work == w.work /\
  (forall (y: obj_addr). L.memP y w0.inbox ==> L.memP y w.inbox) /\
  scan_rec_ok cs g s.heap i w0.scan /\
  entry_ok cs g i x

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let push_record (cs: list nat) (g: heap) (s: state) (i: nat) (w w0: worker) (x: obj_addr)
  : Lemma (requires push_pre cs g s i w w0 x /\ is_white x s.heap)
          (ensures worker_ok cs g (makeGray x s.heap) i ({ w0 with work = x :: w0.work }))
  = makeGray_eq x s.heap;
    makeGray_is_gray x s.heap;
    colors_distinct x s.heap;
    assert (worker_ok cs g s.heap i w);
    assert (~(L.memP x w.work));
    worker_ok_other cs g s.heap i w0 x Gray
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let push_step (cs: list nat) (g: heap) (s: state) (i: nat) (w w0: worker) (x: obj_addr) (e: event)
  : Lemma (requires push_pre cs g s i w w0 x /\ actor e == i)
          (ensures (let (g', w') = grey_push s.heap w0 x in
                    let s' = { s with heap = g'; workers = set_nth s.workers i w' } in
                    inv_own cs g s' /\ writes_own cs g s s' e))
  = nth_lt s.workers i;
    assert (worker_ok cs g s.heap i w);
    if is_white x s.heap then begin
      let g' = makeGray x s.heap in
      makeGray_eq x s.heap;
      colors_distinct x s.heap;
      recoloured_makeGray g s.heap x;
      push_record cs g s i w w0 x;
      others_unaffected cs g s i x Gray;
      replace_worker cs g s i g' ({ w0 with work = x :: w0.work }) s.net;
      FStar.Classical.forall_intro (set_color_writes s.heap x Gray);
      writes_at cs g s ({ s with heap = g'; workers = set_nth s.workers i ({ w0 with work = x :: w0.work }) }) e x
    end else begin
      assert (worker_ok cs g s.heap i w0);
      replace_worker cs g s i s.heap w0 s.net
    end
#pop-options

/// Worker i's record changes, the heap does not.
let move_pre (cs: list nat) (g: heap) (s: state) (i: nat) (w w0: worker) (net': list msg) : prop =
  inv_own cs g s /\ nth s.workers i == Some w /\ w0.work == w.work /\
  (forall (y: obj_addr). L.memP y w0.inbox ==> L.memP y w.inbox \/ entry_ok cs g i y) /\
  scan_rec_ok cs g s.heap i w0.scan /\
  (forall (m: msg). L.memP m net' ==> L.memP m s.net \/ msg_ok cs g m)

#push-options "--z3rlimit 30 --fuel 1 --ifuel 1"
let move_step (cs: list nat) (g: heap) (s: state) (i: nat) (w w0: worker) (net': list msg)
  : Lemma (requires move_pre cs g s i w w0 net')
          (ensures inv_own cs g ({ s with workers = set_nth s.workers i w0; net = net' }))
  = nth_lt s.workers i;
    assert (worker_ok cs g s.heap i w);
    replace_worker cs g s i s.heap w0 net'
#pop-options

/// ---------------------------------------------------------------------------
/// The initial state
/// ---------------------------------------------------------------------------

let rec make_workers_nth (cs: list nat) (g: heap) (roots: list obj_addr) (i n j: nat)
  : Lemma (ensures L.length (make_workers cs g roots i n) == n /\
                   nth (make_workers cs g roots i n) j ==
                   (if j < n then Some { work = []; inbox = owned_roots cs g (i + j) roots; scan = None }
                    else None))
          (decreases n)
  = if n = 0 then () else if j = 0 then make_workers_nth cs g roots (i + 1) (n - 1) 0
    else make_workers_nth cs g roots (i + 1) (n - 1) (j - 1)

let rec owned_roots_mem (cs: list nat) (g: heap) (i: nat) (roots: list obj_addr) (y: obj_addr)
  : Lemma (requires L.memP y (owned_roots cs g i roots))
          (ensures owner cs y == i /\
                   (exists (r: obj_addr). L.memP r roots /\ y == resolve_object r g))
          (decreases roots)
  = match roots with
    | [] -> ()
    | r :: rest ->
      if owner cs (resolve_x r g) = i && y = resolve_x r g then ()
      else owned_roots_mem cs g i rest y

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let init_own (cs: list nat) (g: heap) (roots: list obj_addr)
  : Lemma (requires mark_pre g roots)
          (ensures inv_own cs g (init cs g roots))
  = let s = init cs g roots in
    recoloured_refl g;
    make_workers_nth cs g roots 0 (nranges cs) 0;
    let wk (i: nat) (w: worker)
      : Lemma (requires nth s.workers i == Some w) (ensures worker_ok cs g s.heap i w)
      = make_workers_nth cs g roots 0 (nranges cs) i;
        let inb (x: obj_addr) : Lemma (requires L.memP x w.inbox) (ensures entry_ok cs g i x) =
          owned_roots_mem cs g i roots x;
          let r = FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
                    (fun r -> L.memP r roots /\ x == resolve_object r g) in
          colors_distinct x g
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires inb)
    in
    FStar.Classical.forall_intro_2 (fun i w -> FStar.Classical.move_requires (wk i) w)
#pop-options

/// ---------------------------------------------------------------------------
/// The steps
/// ---------------------------------------------------------------------------

let pop_worker (s: state) (w: worker) (x: obj_addr) (rest: list obj_addr) : worker =
  let ws = wosize_x x s.heap in
  let sc = if is_no_scan_x x s.heap || U64.v ws = 0 then None
           else Some ({ sobj = x; snext = 1UL; sws = ws } <: scanning) in
  { w with work = rest; scan = sc }

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let pop_record (cs: list nat) (g: heap) (s: state) (i: nat) (w: worker) (x: obj_addr) (rest: list obj_addr)
  : Lemma (requires inv_own cs g s /\ nth s.workers i == Some w /\ w.scan == None /\ w.work == x :: rest)
          (ensures worker_ok cs g (makeBlack x s.heap) i (pop_worker s w x rest) /\
                   entry_ok cs g i x /\ is_gray x s.heap)
  = assert (worker_ok cs g s.heap i w);
    assert (L.memP x w.work);
    colors_distinct x s.heap;
    makeBlack_eq x s.heap;
    makeBlack_is_black x s.heap;
    recoloured_wosize g s.heap x;
    recoloured_no_scan g s.heap x;
    recoloured_blue g s.heap x;
    let aux (y: obj_addr) : Lemma (requires L.memP y rest) (ensures is_gray y (makeBlack x s.heap)) =
      other_color s.heap x y Black in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let step_pop (cs: list nat) (g: heap) (s: state) (i: nat)
  : Lemma (requires inv_own cs g s)
          (ensures inv_own cs g (step cs s (Pop i)) /\ writes_own cs g s (step cs s (Pop i)) (Pop i))
  = match nth s.workers i with
    | None -> ()
    | Some w ->
      match w.scan, w.work with
      | None, x :: rest ->
        nth_lt s.workers i;
        let w' = pop_worker s w x rest in
        let h' = makeBlack x s.heap in
        let s' = { s with heap = h'; workers = set_nth s.workers i w'; net = s.net } in
        assert (step cs s (Pop i) == s');
        pop_record cs g s i w x rest;
        colors_distinct x s.heap;
        makeBlack_eq x s.heap;
        recoloured_makeBlack g s.heap x;
        others_unaffected cs g s i x Black;
        replace_worker cs g s i h' w' s.net;
        FStar.Classical.forall_intro (set_color_writes s.heap x Black);
        writes_at cs g s s' (Pop i) x
      | _ -> ()
#pop-options

/// The object field `snext` of the scanned object names, if it is a pointer.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let scan_child (cs: list nat) (g: heap) (s: state) (i: nat) (w: worker) (sc: scanning)
  : Lemma (requires inv_own cs g s /\ nth s.workers i == Some w /\ w.scan == Some sc)
          (ensures (let v = get_field_x s.heap sc.sobj sc.snext in
                    HeapGraph.is_pointer_field v ==>
                    (HeapGraph.is_pointer_field_is_obj_addr v;
                     let c = resolve_x v s.heap in
                     Seq.mem c (objs g) /\ ~(is_blue c g))))
  = assert (worker_ok cs g s.heap i w);
    let v = get_field_x s.heap sc.sobj sc.snext in
    if HeapGraph.is_pointer_field v then begin
      recoloured_wosize g s.heap sc.sobj;
      recoloured_no_scan g s.heap sc.sobj;
      colors_distinct sc.sobj s.heap;
      F.field_child_facts s.heap sc.sobj sc.snext;
      HeapGraph.is_pointer_field_is_obj_addr v;
      recoloured_blue g s.heap (resolve_x v s.heap)
    end
#pop-options

let send_ok (cs: list nat) (g: heap) (net: list msg) (m: msg)
  : Lemma (requires msg_ok cs g m)
          (ensures forall (m': msg). L.memP m' (net @ [m]) ==> L.memP m' net \/ msg_ok cs g m')
  = FStar.Classical.forall_intro (fun m' -> L.append_memP net [m] m')

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let step_scan (cs: list nat) (g: heap) (s: state) (i: nat)
  : Lemma (requires inv_own cs g s)
          (ensures inv_own cs g (step cs s (Scan i)) /\ writes_own cs g s (step cs s (Scan i)) (Scan i))
  = match nth s.workers i with
    | None -> ()
    | Some w ->
      match w.scan with
      | None -> ()
      | Some sc ->
        assert (worker_ok cs g s.heap i w);
        let w0 = { w with scan = next_field sc } in
        scan_next_ok cs g s.heap i sc;
        scan_child cs g s i w sc;
        let v = get_field_x s.heap sc.sobj sc.snext in
        if HeapGraph.is_pointer_field v then begin
          HeapGraph.is_pointer_field_is_obj_addr v;
          let c = resolve_x v s.heap in
          if owner cs c = i then begin
            push_step cs g s i w w0 c (Scan i);
            let (g', w') = grey_push s.heap w0 c in
            assert (step cs s (Scan i) == { s with heap = g'; workers = set_nth s.workers i w' })
          end else begin
            let m = { dest = owner cs c; addr = c } in
            assert (msg_ok cs g m);
            send_ok cs g s.net m;
            assert (scan_rec_ok cs g s.heap i w0.scan);
            assert (move_pre cs g s i w w0 (s.net @ [m]));
            move_step cs g s i w w0 (s.net @ [m]);
            assert (step cs s (Scan i) == { s with workers = set_nth s.workers i w0; net = s.net @ [m] })
          end
        end else begin
          move_step cs g s i w w0 s.net;
          assert (step cs s (Scan i) == { s with workers = set_nth s.workers i w0; net = s.net })
        end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let step_take (cs: list nat) (g: heap) (s: state) (i: nat)
  : Lemma (requires inv_own cs g s)
          (ensures inv_own cs g (step cs s (Take i)) /\ writes_own cs g s (step cs s (Take i)) (Take i))
  = match nth s.workers i with
    | None -> ()
    | Some w ->
      match w.inbox with
      | [] -> ()
      | x :: rest ->
        assert (worker_ok cs g s.heap i w);
        assert (L.memP x w.inbox);
        let w0 = { w with inbox = rest } in
        push_step cs g s i w w0 x (Take i);
        let (g', w') = grey_push s.heap w0 x in
        assert (step cs s (Take i) == { s with heap = g'; workers = set_nth s.workers i w' })
#pop-options

let append_entry (cs: list nat) (g: heap) (l: list obj_addr) (i: nat) (x y: obj_addr)
  : Lemma (requires entry_ok cs g i x /\ L.memP y (l @ [x]))
          (ensures L.memP y l \/ entry_ok cs g i y)
  = L.append_memP l [x] y

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let deliver_pre (cs: list nat) (g: heap) (s: state) (j: nat) (m: msg) (w: worker)
  : Lemma (requires inv_own cs g s /\ nth s.net j == Some m /\ nth s.workers m.dest == Some w)
          (ensures move_pre cs g s m.dest w ({ w with inbox = w.inbox @ [m.addr] }) (remove_nth s.net j))
  = nth_memP s.net j m;
    assert (msg_ok cs g m);
    assert (worker_ok cs g s.heap m.dest w);
    assert (entry_ok cs g m.dest m.addr);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (append_entry cs g w.inbox m.dest m.addr));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (memP_remove_nth s.net j))
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let step_deliver (cs: list nat) (g: heap) (s: state) (j: nat)
  : Lemma (requires inv_own cs g s)
          (ensures inv_own cs g (step cs s (Deliver j)) /\
                   writes_own cs g s (step cs s (Deliver j)) (Deliver j))
  = match nth s.net j with
    | None -> ()
    | Some m ->
      match nth s.workers m.dest with
      | None -> ()
      | Some w ->
        let w0 = { w with inbox = w.inbox @ [m.addr] } in
        deliver_pre cs g s j m w;
        move_step cs g s m.dest w w0 (remove_nth s.net j);
        assert (step cs s (Deliver j) ==
                { s with workers = set_nth s.workers m.dest w0; net = remove_nth s.net j })
#pop-options

let step_own (cs: list nat) (g: heap) (s: state) (e: event)
  : Lemma (requires inv_own cs g s)
          (ensures inv_own cs g (step cs s e) /\ writes_own cs g s (step cs s e) e)
  = match e with
    | Pop i -> step_pop cs g s i
    | Scan i -> step_scan cs g s i
    | Take i -> step_take cs g s i
    | Deliver j -> step_deliver cs g s j

let rec run_from_own (cs: list nat) (g: heap) (s: state) (sched: list event)
  : Lemma (requires inv_own cs g s)
          (ensures inv_own cs g (run_from cs s sched))
          (decreases sched)
  = match sched with
    | [] -> ()
    | e :: rest -> step_own cs g s e; run_from_own cs g (step cs s e) rest

let run_own (cs: list nat) (g: heap) (roots: list obj_addr) (sched: list event)
  : Lemma (requires mark_pre g roots)
          (ensures inv_own cs g (run cs g roots sched))
  = init_own cs g roots;
    run_from_own cs g (init cs g roots) sched
