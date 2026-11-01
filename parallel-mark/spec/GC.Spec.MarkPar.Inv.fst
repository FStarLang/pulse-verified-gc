/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar.Inv — the marking invariant
///
/// On top of the ownership invariant (`GC.Spec.MarkPar.Own`), in every state
/// a run reaches:
///   * every grey object is on its owner's work list               (grey_ok)
///   * every grey or black object, every inbox entry and every
///     message is reachable from the roots                         (sound)
///   * every root object is non-white, or pending: in its owner's
///     inbox or in a message                                       (roots_ok)
///   * for every pointer field j of a black scannable object x, the
///     object it names is non-white, or pending, or x's owner is
///     part-way through x and has not reached field j yet          (black_ok)
/// When marking has ended nothing is pending, no worker is part-way through
/// an object, and no work list holds anything; so there is no grey object,
/// every root object is black, and no black object points to a white one.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar.Inv

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
open GC.Spec.MarkPar.Model
open GC.Spec.MarkPar.Recolour

module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module F = GC.Spec.MarkPar.Field
module Own = GC.Spec.MarkPar.Own
module R = GC.Spec.MarkPar.Roots

/// ---------------------------------------------------------------------------
/// Definitions
/// ---------------------------------------------------------------------------

let objs (g: heap) = objects zero_addr g

let work_at (s: state) (i: nat) : list obj_addr =
  match nth s.workers i with Some w -> w.work | None -> []

let inbox_at (s: state) (i: nat) : list obj_addr =
  match nth s.workers i with Some w -> w.inbox | None -> []

let scan_at (s: state) (i: nat) : option scanning =
  match nth s.workers i with Some w -> w.scan | None -> None

/// c is waiting to be taken: in its owner's inbox, or in a message.
let pending (cs: list nat) (s: state) (c: obj_addr) : prop =
  L.memP c (inbox_at s (owner cs c)) \/ (exists (m: msg). L.memP m s.net /\ m.addr == c)

/// x's owner is part-way through x, at or before field j.
let unscanned (cs: list nat) (s: state) (x: obj_addr) (j: nat) : prop =
  match scan_at s (owner cs x) with
  | Some sc -> sc.sobj == x /\ U64.v sc.snext <= j
  | None -> False

/// The object field j of x names, in g.
let field_target (g: heap) (x: obj_addr) (j: U64.t{U64.v j >= 1}) : GTot obj_addr =
  let v = HeapGraph.get_field g x j in
  if HeapGraph.is_pointer_field v then begin
    HeapGraph.is_pointer_field_is_obj_addr v;
    resolve_object v g
  end else x

let is_field (g: heap) (x: obj_addr) (j: U64.t{U64.v j >= 1}) : prop =
  Seq.mem x (objs g) /\ ~(is_no_scan x g) /\ ~(is_blue x g) /\
  U64.v j <= U64.v (wosize_of_object x g) /\
  HeapGraph.is_pointer_field (HeapGraph.get_field g x j)

[@@"opaque_to_smt"]
let grey_ok (cs: list nat) (g: heap) (s: state) : prop =
  forall (x: obj_addr). Seq.mem x (objs g) /\ is_gray x s.heap ==>
    L.memP x (work_at s (owner cs x))

[@@"opaque_to_smt"]
let sound (cs: list nat) (g: heap) (roots: list obj_addr) (s: state) : prop =
  (forall (x: obj_addr). Seq.mem x (objs g) /\ (is_gray x s.heap \/ is_black x s.heap) ==>
     reachable g roots x) /\
  (forall (i: nat) (y: obj_addr). L.memP y (inbox_at s i) ==> reachable g roots y) /\
  (forall (m: msg). L.memP m s.net ==> reachable g roots m.addr)

[@@"opaque_to_smt"]
let roots_ok (cs: list nat) (g: heap) (roots: list obj_addr) (s: state) : prop =
  forall (r: obj_addr). L.memP r (root_objs g roots) ==> ~(is_white r s.heap) \/ pending cs s r

[@@"opaque_to_smt"]
let black_ok (cs: list nat) (g: heap) (s: state) : prop =
  forall (x: obj_addr) (j: U64.t{U64.v j >= 1}).
    is_field g x j /\ is_black x s.heap ==>
    ~(is_white (field_target g x j) s.heap) \/ pending cs s (field_target g x j) \/
    unscanned cs s x (U64.v j)

/// The ownership invariant, kept out of sight unless revealed.
[@@"opaque_to_smt"]
let own (cs: list nat) (g: heap) (s: state) : prop = Own.inv_own cs g s

let inv_mark (cs: list nat) (g: heap) (roots: list obj_addr) (s: state) : prop =
  own cs g s /\ grey_ok cs g s /\ sound cs g roots s /\
  roots_ok cs g roots s /\ black_ok cs g s

/// The setting every lemma here assumes.
[@@"opaque_to_smt"]
let ctx (cs: list nat) (g: heap) (roots: list obj_addr) : prop =
  mark_pre g roots /\ graph_pre g roots

/// ---------------------------------------------------------------------------
/// The initial state
/// ---------------------------------------------------------------------------

let rec count_le_lt (cs: list nat) (a: nat)
  : Lemma (ensures count_le cs a <= L.length cs) (decreases cs)
  = match cs with [] -> () | _ :: r -> count_le_lt r a

/// A root's object is in its owner's initial inbox.
let rec owned_roots_has (cs: list nat) (g: heap) (roots: list obj_addr) (r: obj_addr)
  : Lemma (requires L.memP r roots)
          (ensures L.memP (resolve_object r g)
                     (owned_roots cs g (owner cs (resolve_object r g)) roots))
          (decreases roots)
  = match roots with
    | [] -> ()
    | h :: t -> if h = r then () else owned_roots_has cs g t r

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let init_mark (cs: list nat) (g: heap) (roots: list obj_addr)
  : Lemma (requires ctx cs g roots)
          (ensures inv_mark cs g roots (init cs g roots))
  = let s = init cs g roots in
    reveal_opaque (`%ctx) (ctx cs g roots);
    reveal_opaque (`%own) (own cs g s);
    reveal_opaque (`%grey_ok) (grey_ok cs g s);
    reveal_opaque (`%sound) (sound cs g roots s);
    reveal_opaque (`%roots_ok) (roots_ok cs g roots s);
    reveal_opaque (`%black_ok) (black_ok cs g s);
    Own.init_own cs g roots;
    let at (i: nat) : Lemma (inbox_at s i ==
        (if i < nranges cs then owned_roots cs g i roots else [])) =
      Own.make_workers_nth cs g roots 0 (nranges cs) i in
    FStar.Classical.forall_intro at;
    let col (x: obj_addr) : Lemma (requires Seq.mem x (objs g))
        (ensures ~(is_gray x g) /\ ~(is_black x g)) = () in
    FStar.Classical.forall_intro (FStar.Classical.move_requires col);
    let inb (i: nat) (y: obj_addr)
      : Lemma (requires L.memP y (inbox_at s i)) (ensures reachable g roots y)
      = at i;
        Own.owned_roots_mem cs g i roots y;
        R.root_objs_mem g roots y;
        R.root_reachable g roots y
    in
    FStar.Classical.forall_intro_2 (fun i y -> FStar.Classical.move_requires (inb i) y);
    let rt (r: obj_addr)
      : Lemma (requires L.memP r (root_objs g roots)) (ensures pending cs s r)
      = R.root_objs_mem g roots r;
        let r0 = FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
                   (fun r0 -> L.memP r0 roots /\ r == resolve_object r0 g) in
        owned_roots_has cs g roots r0;
        R.root_obj_facts g roots r;
        Own.init_own cs g roots;
        at (owner cs r);
        // r's owner is a real worker: owner < nranges
        count_le_lt cs (U64.v (hd_address r))
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires rt)
#pop-options

/// ---------------------------------------------------------------------------
/// Facts every step lemma uses
/// ---------------------------------------------------------------------------

let colors (x: obj_addr) (h: heap)
  : Lemma ((is_white x h ==> ~(is_gray x h) /\ ~(is_black x h) /\ ~(is_blue x h)) /\
           (is_gray x h ==> ~(is_black x h) /\ ~(is_blue x h)) /\
           (is_black x h ==> ~(is_blue x h)) /\
           (is_white x h \/ is_gray x h \/ is_black x h \/ is_blue x h))
  = is_white_iff x h; is_gray_iff x h; is_black_iff x h; is_blue_iff x h

/// One colour change: other objects keep their colour.
let others_keep (h: heap) (x: obj_addr) (c: color)
  : Lemma (forall (y: obj_addr). y <> x ==>
             is_gray y (set_object_color x h c) == is_gray y h /\
             is_black y (set_object_color x h c) == is_black y h /\
             is_white y (set_object_color x h c) == is_white y h)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (fun y -> Own.other_color h x y c))

/// In a recoloured heap, the field read in h is the field read in g.
let field_in (g h: heap) (x: obj_addr) (j: U64.t{U64.v j >= 1})
  : Lemma (requires recoloured g h /\ Seq.mem x (objs g) /\ U64.v j <= U64.v (wosize_of_object x g))
          (ensures HeapGraph.get_field h x j == HeapGraph.get_field g x j)
  = ()

/// Pending stays pending while no inbox entry or message is lost.
let pending_mono (cs: list nat) (s s': state) (c: obj_addr)
  : Lemma (requires pending cs s c /\
                    (forall (y: obj_addr). L.memP y (inbox_at s (owner cs c)) ==>
                                           L.memP y (inbox_at s' (owner cs c))) /\
                    (forall (m: msg). L.memP m s.net ==> L.memP m s'.net))
          (ensures pending cs s' c)
  = ()

let append_sub (net: list msg) (m: msg)
  : Lemma (forall (m': msg). L.memP m' net ==> L.memP m' (net @ [m]))
  = FStar.Classical.forall_intro (fun m' -> L.append_memP net [m] m')

/// ---------------------------------------------------------------------------
/// Pop
/// ---------------------------------------------------------------------------

/// s' is s after worker i pops x (leaving rest) and starts on sc'.
let pop_rel (cs: list nat) (g: heap) (s s': state) (i: nat) (x: obj_addr) (rest: list obj_addr)
    (sc': option scanning) : prop =
  s'.heap == set_object_color x s.heap Black /\ s'.net == s.net /\
  (forall (j: nat). inbox_at s' j == inbox_at s j) /\
  (forall (j: nat). work_at s' j == (if j = i then rest else work_at s j)) /\
  (forall (j: nat). scan_at s' j == (if j = i then sc' else scan_at s j)) /\
  scan_at s i == None /\ work_at s i == x :: rest /\
  (match sc' with
   | None -> is_no_scan x g \/ wosize_of_object x g == 0UL
   | Some sc -> sc.sobj == x /\ sc.snext == 1UL /\ sc.sws == wosize_of_object x g)

/// What the ownership invariant says about the popped object.
let pop_x (cs: list nat) (g: heap) (s: state) (i: nat) (x: obj_addr) (rest: list obj_addr)
  : Lemma (requires Own.inv_own cs g s /\ work_at s i == x :: rest)
          (ensures Seq.mem x (objs g) /\ owner cs x == i /\ is_gray x s.heap /\ ~(L.memP x rest))
  = match nth s.workers i with
    | Some w -> assert (Own.worker_ok cs g s.heap i w)
    | None -> ()

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let pop_grey (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (i: nat)
    (x: obj_addr) (rest: list obj_addr) (sc': option scanning)
  : Lemma (requires inv_mark cs g roots s /\ pop_rel cs g s s' i x rest sc')
          (ensures grey_ok cs g s')
  = reveal_opaque (`%own) (own cs g s);
    reveal_opaque (`%grey_ok) (grey_ok cs g s);
    reveal_opaque (`%grey_ok) (grey_ok cs g s');
    pop_x cs g s i x rest;
    others_keep s.heap x Black;
    makeBlack_eq x s.heap; makeBlack_is_black x s.heap;
    colors x s'.heap
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let pop_sound (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (i: nat)
    (x: obj_addr) (rest: list obj_addr) (sc': option scanning)
  : Lemma (requires inv_mark cs g roots s /\ pop_rel cs g s s' i x rest sc')
          (ensures sound cs g roots s' /\ roots_ok cs g roots s')
  = reveal_opaque (`%own) (own cs g s);
    reveal_opaque (`%sound) (sound cs g roots s);
    reveal_opaque (`%sound) (sound cs g roots s');
    reveal_opaque (`%roots_ok) (roots_ok cs g roots s);
    reveal_opaque (`%roots_ok) (roots_ok cs g roots s');
    pop_x cs g s i x rest;
    others_keep s.heap x Black;
    colors x s.heap;
    makeBlack_eq x s.heap; makeBlack_is_black x s.heap;
    colors x s'.heap;
    let rt (r: obj_addr)
      : Lemma (requires L.memP r (root_objs g roots))
              (ensures ~(is_white r s'.heap) \/ pending cs s' r)
      = assert (~(is_white r s.heap) \/ pending cs s r);
        assert (inbox_at s' (owner cs r) == inbox_at s (owner cs r));
        if r = x then () else ()
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires rt)
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let pop_black (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (i: nat)
    (x: obj_addr) (rest: list obj_addr) (sc': option scanning)
  : Lemma (requires inv_mark cs g roots s /\ pop_rel cs g s s' i x rest sc')
          (ensures black_ok cs g s')
  = reveal_opaque (`%own) (own cs g s);
    reveal_opaque (`%black_ok) (black_ok cs g s);
    reveal_opaque (`%black_ok) (black_ok cs g s');
    pop_x cs g s i x rest;
    others_keep s.heap x Black;
    colors x s.heap;
    let aux (y: obj_addr) (j: U64.t{U64.v j >= 1})
      : Lemma (requires is_field g y j /\ is_black y s'.heap)
              (ensures ~(is_white (field_target g y j) s'.heap) \/ pending cs s' (field_target g y j) \/
                       unscanned cs s' y (U64.v j))
      = let c = field_target g y j in
        if y = x then begin
          assert (scan_at s' i == sc');
          match sc' with
          | Some sc -> assert (unscanned cs s' y (U64.v j))
          | None -> ()
        end else begin
          assert (is_black y s.heap);
          assert (~(is_white c s.heap) \/ pending cs s c \/ unscanned cs s y (U64.v j));
          colors c s.heap;
          colors c s'.heap;
          makeBlack_eq x s.heap; makeBlack_is_black x s.heap;
          assert (~(is_white c s.heap) ==> ~(is_white c s'.heap));
          assert (inbox_at s' (owner cs c) == inbox_at s (owner cs c));
          assert (pending cs s c ==> pending cs s' c);
          assert (scan_at s' (owner cs y) == (if owner cs y = i then sc' else scan_at s (owner cs y)));
          assert (unscanned cs s y (U64.v j) ==> unscanned cs s' y (U64.v j))
        end
    in
    FStar.Classical.forall_intro_2 (fun y j -> FStar.Classical.move_requires (aux y) j)
#pop-options

/// ---------------------------------------------------------------------------
/// Scan
/// ---------------------------------------------------------------------------

/// s' is s after worker i, part-way through sc, looks at field sc.snext.
/// out 0: nothing changes but the position (not a pointer, or a non-white
/// object i owns); out 1: i greys and pushes its white object c; out 2: i
/// sends c to its owner.
let scan_rel (cs: list nat) (g: heap) (s s': state) (i: nat) (sc: scanning) (out: nat{out <= 2}) : prop =
  scan_at s i == Some sc /\
  (forall (j: nat). inbox_at s' j == inbox_at s j) /\
  (forall (j: nat). j <> i ==> scan_at s' j == scan_at s j /\ work_at s' j == work_at s j) /\
  scan_at s' i == next_field sc /\
  (let c = field_target g sc.sobj sc.snext in
   (out = 0 ==> s'.heap == s.heap /\ s'.net == s.net /\ work_at s' i == work_at s i /\
                (is_field g sc.sobj sc.snext ==> ~(is_white c s.heap))) /\
   (out = 1 ==> is_field g sc.sobj sc.snext /\ owner cs c == i /\ is_white c s.heap /\
                s'.heap == set_object_color c s.heap Gray /\ s'.net == s.net /\
                work_at s' i == c :: work_at s i) /\
   (out = 2 ==> is_field g sc.sobj sc.snext /\ owner cs c <> i /\
                s'.heap == s.heap /\ s'.net == s.net @ [{ dest = owner cs c; addr = c }] /\
                work_at s' i == work_at s i))

/// The scanned object, per the ownership invariant.
let scan_x (cs: list nat) (g: heap) (s: state) (i: nat) (sc: scanning)
  : Lemma (requires Own.inv_own cs g s /\ scan_at s i == Some sc)
          (ensures Seq.mem sc.sobj (objs g) /\ owner cs sc.sobj == i /\ is_black sc.sobj s.heap /\
                   ~(is_no_scan sc.sobj g) /\ ~(is_blue sc.sobj g) /\
                   1 <= U64.v sc.snext /\ U64.v sc.snext <= U64.v sc.sws /\
                   sc.sws == wosize_of_object sc.sobj g)
  = match nth s.workers i with
    | Some w -> assert (Own.worker_ok cs g s.heap i w); colors sc.sobj s.heap
    | None -> ()

/// The object a scanned pointer field names is enumerated, and reachable if
/// the scanned object is.
#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let target_facts (cs: list nat) (g: heap) (roots: list obj_addr) (x: obj_addr) (j: U64.t{U64.v j >= 1})
  : Lemma (requires ctx cs g roots /\ is_field g x j)
          (ensures Seq.mem (field_target g x j) (objs g) /\ ~(is_blue (field_target g x j) g) /\
                   (reachable g roots x ==> reachable g roots (field_target g x j)))
  = reveal_opaque (`%ctx) (ctx cs g roots);
    F.field_child_facts g x j;
    let c = field_target g x j in
    FStar.Classical.move_requires (R.edge_reachable g roots x) c
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let scan_grey (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (i: nat)
    (sc: scanning) (out: nat{out <= 2})
  : Lemma (requires inv_mark cs g roots s /\ scan_rel cs g s s' i sc out)
          (ensures grey_ok cs g s')
  = reveal_opaque (`%grey_ok) (grey_ok cs g s);
    reveal_opaque (`%grey_ok) (grey_ok cs g s');
    let c = field_target g sc.sobj sc.snext in
    if out = 1 then begin
      others_keep s.heap c Gray;
      makeGray_eq c s.heap; makeGray_is_gray c s.heap
    end
#pop-options

let net_append_reach (g: heap) (roots: list obj_addr) (net: list msg) (m: msg)
  : Lemma (requires (forall (m': msg). L.memP m' net ==> reachable g roots m'.addr) /\
                    reachable g roots m.addr)
          (ensures forall (m': msg). L.memP m' (net @ [m]) ==> reachable g roots m'.addr)
  = FStar.Classical.forall_intro (fun m' -> L.append_memP net [m] m')

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let scan_sound_grey (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (i: nat) (sc: scanning)
  : Lemma (requires ctx cs g roots /\ inv_mark cs g roots s /\ scan_rel cs g s s' i sc 1)
          (ensures sound cs g roots s')
  = reveal_opaque (`%own) (own cs g s);
    reveal_opaque (`%sound) (sound cs g roots s);
    reveal_opaque (`%sound) (sound cs g roots s');
    let x = sc.sobj in
    let c = field_target g x sc.snext in
    scan_x cs g s i sc;
    assert (is_field g x sc.snext);
    target_facts cs g roots x sc.snext;
    others_keep s.heap c Gray;
    makeGray_eq c s.heap; makeGray_is_gray c s.heap;
    colors c s'.heap
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let scan_sound_send (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (i: nat) (sc: scanning)
  : Lemma (requires ctx cs g roots /\ inv_mark cs g roots s /\ scan_rel cs g s s' i sc 2)
          (ensures sound cs g roots s')
  = reveal_opaque (`%own) (own cs g s);
    reveal_opaque (`%sound) (sound cs g roots s);
    reveal_opaque (`%sound) (sound cs g roots s');
    let x = sc.sobj in
    let c = field_target g x sc.snext in
    scan_x cs g s i sc;
    assert (is_field g x sc.snext);
    target_facts cs g roots x sc.snext;
    net_append_reach g roots s.net ({ dest = owner cs c; addr = c })
#pop-options

let scan_net (cs: list nat) (g: heap) (s s': state) (i: nat) (sc: scanning) (out: nat{out <= 2})
  : Lemma (requires scan_rel cs g s s' i sc out)
          (ensures forall (m: msg). L.memP m s.net ==> L.memP m s'.net)
  = let c = field_target g sc.sobj sc.snext in
    if out = 2 then append_sub s.net ({ dest = owner cs c; addr = c })
    else assert (s'.net == s.net)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let scan_roots (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (i: nat)
    (sc: scanning) (out: nat{out <= 2})
  : Lemma (requires inv_mark cs g roots s /\ scan_rel cs g s s' i sc out)
          (ensures roots_ok cs g roots s')
  = reveal_opaque (`%roots_ok) (roots_ok cs g roots s);
    reveal_opaque (`%roots_ok) (roots_ok cs g roots s');
    let c = field_target g sc.sobj sc.snext in
    if out = 1 then begin
      others_keep s.heap c Gray;
      makeGray_eq c s.heap; makeGray_is_gray c s.heap;
      colors c s'.heap
    end;
    if out = 2 then
      FStar.Classical.forall_intro (fun m -> L.append_memP s.net [{ dest = owner cs c; addr = c }] m);
    let rt (r: obj_addr)
      : Lemma (requires L.memP r (root_objs g roots))
              (ensures ~(is_white r s'.heap) \/ pending cs s' r)
      = assert (~(is_white r s.heap) \/ pending cs s r);
        assert (inbox_at s' (owner cs r) == inbox_at s (owner cs r));
        scan_net cs g s s' i sc out;
        FStar.Classical.move_requires (pending_mono cs s s') r;
        colors r s.heap;
        assert (~(is_white r s.heap) ==> ~(is_white r s'.heap))
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires rt)
#pop-options

let scan_sound_none (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (i: nat) (sc: scanning)
  : Lemma (requires sound cs g roots s /\ scan_rel cs g s s' i sc 0)
          (ensures sound cs g roots s')
  = reveal_opaque (`%sound) (sound cs g roots s);
    reveal_opaque (`%sound) (sound cs g roots s');
    ()

let scan_sound (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (i: nat)
    (sc: scanning) (out: nat{out <= 2})
  : Lemma (requires ctx cs g roots /\ inv_mark cs g roots s /\ scan_rel cs g s s' i sc out)
          (ensures sound cs g roots s' /\ roots_ok cs g roots s')
  = scan_roots cs g roots s s' i sc out;
    if out = 1 then scan_sound_grey cs g roots s s' i sc
    else if out = 2 then scan_sound_send cs g roots s s' i sc
    else begin
      assert (out == 0);
      scan_sound_none cs g roots s s' i sc
    end

let unscanned_b (cs: list nat) (s: state) (x: obj_addr) (j: nat) : GTot bool =
  match scan_at s (owner cs x) with
  | Some sc -> sc.sobj = x && U64.v sc.snext <= j
  | None -> false

/// One instance of black_ok.
let black_ok_at (cs: list nat) (g: heap) (s: state) (y: obj_addr) (j: U64.t{U64.v j >= 1})
  : Lemma (requires black_ok cs g s /\ is_field g y j /\ is_black y s.heap)
          (ensures ~(is_white (field_target g y j) s.heap) \/ pending cs s (field_target g y j) \/
                   unscanned cs s y (U64.v j))
  = reveal_opaque (`%black_ok) (black_ok cs g s)

/// Scan: what persists from s to s'.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let scan_keeps (cs: list nat) (g: heap) (s s': state) (i: nat) (sc: scanning) (out: nat{out <= 2})
    (d: obj_addr)
  : Lemma (requires scan_rel cs g s s' i sc out)
          (ensures (~(is_white d s.heap) ==> ~(is_white d s'.heap)) /\
                   (is_black d s'.heap ==> is_black d s.heap) /\
                   (pending cs s d ==> pending cs s' d))
  = let c = field_target g sc.sobj sc.snext in
    scan_net cs g s s' i sc out;
    assert (inbox_at s' (owner cs d) == inbox_at s (owner cs d));
    FStar.Classical.move_requires (pending_mono cs s s') d;
    if out = 1 then begin
      makeGray_eq c s.heap; makeGray_is_gray c s.heap;
      colors c s'.heap; colors c s.heap; colors d s.heap;
      if d <> c then Own.other_color s.heap c d Gray
    end
#pop-options

/// Scan: a field other than the one just looked at keeps its cover.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let scan_other_field (cs: list nat) (g: heap) (s s': state) (i: nat) (sc: scanning)
    (out: nat{out <= 2}) (y: obj_addr) (j: nat)
  : Lemma (requires scan_rel cs g s s' i sc out /\ owner cs sc.sobj == i /\
                    unscanned cs s y j /\ (y <> sc.sobj \/ j < U64.v sc.snext))
          (ensures unscanned cs s' y j)
  = ()
#pop-options

/// Scan: the field just looked at is covered.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let scan_this_field (cs: list nat) (g: heap) (s s': state) (i: nat) (sc: scanning)
    (out: nat{out <= 2})
  : Lemma (requires scan_rel cs g s s' i sc out /\ is_field g sc.sobj sc.snext)
          (ensures (let c = field_target g sc.sobj sc.snext in
                    ~(is_white c s'.heap) \/ pending cs s' c))
  = let c = field_target g sc.sobj sc.snext in
    if out = 1 then begin
      makeGray_eq c s.heap; makeGray_is_gray c s.heap; colors c s'.heap
    end else if out = 2 then begin
      append_sub s.net ({ dest = owner cs c; addr = c });
      L.append_memP s.net [{ dest = owner cs c; addr = c }] ({ dest = owner cs c; addr = c })
    end
#pop-options

/// Scan: fields after the one just looked at are still to come.
#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let scan_later_field (cs: list nat) (g: heap) (s s': state) (i: nat) (sc: scanning)
    (out: nat{out <= 2}) (j: nat)
  : Lemma (requires scan_rel cs g s s' i sc out /\ owner cs sc.sobj == i /\
                    U64.v sc.snext < j /\ j <= U64.v sc.sws)
          (ensures unscanned cs s' sc.sobj j)
  = ()
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let scan_black (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (i: nat)
    (sc: scanning) (out: nat{out <= 2})
  : Lemma (requires ctx cs g roots /\ inv_mark cs g roots s /\ scan_rel cs g s s' i sc out)
          (ensures black_ok cs g s')
  = reveal_opaque (`%own) (own cs g s);
    reveal_opaque (`%black_ok) (black_ok cs g s');
    let x = sc.sobj in
    let f = sc.snext in
    scan_x cs g s i sc;
    let aux (y: obj_addr) (j: U64.t{U64.v j >= 1})
      : Lemma (requires is_field g y j /\ is_black y s'.heap)
              (ensures ~(is_white (field_target g y j) s'.heap) \/ pending cs s' (field_target g y j) \/
                       unscanned cs s' y (U64.v j))
      = let d = field_target g y j in
        scan_keeps cs g s s' i sc out y;
        scan_keeps cs g s s' i sc out d;
        if y = x && U64.v j = U64.v f then begin
          U64.v_inj j f;
          scan_this_field cs g s s' i sc out
        end else if y = x && U64.v j > U64.v f then
          scan_later_field cs g s s' i sc out (U64.v j)
        else begin
          black_ok_at cs g s y j;
          if unscanned_b cs s y (U64.v j) then
            scan_other_field cs g s s' i sc out y (U64.v j)
        end
    in
    FStar.Classical.forall_intro_2 (fun y j -> FStar.Classical.move_requires (aux y) j)
#pop-options

/// ---------------------------------------------------------------------------
/// Take
/// ---------------------------------------------------------------------------

/// s' is s after worker i takes x from its inbox; out 1 if x was white
/// and is now greyed and pushed.
let take_rel (cs: list nat) (g: heap) (s s': state) (i: nat) (x: obj_addr) (rest: list obj_addr)
    (out: nat{out <= 1}) : prop =
  inbox_at s i == x :: rest /\ inbox_at s' i == rest /\
  (forall (j: nat). j <> i ==> inbox_at s' j == inbox_at s j /\ work_at s' j == work_at s j) /\
  (forall (j: nat). scan_at s' j == scan_at s j) /\
  s'.net == s.net /\
  (out = 1 ==> is_white x s.heap /\ s'.heap == set_object_color x s.heap Gray /\
               work_at s' i == x :: work_at s i) /\
  (out = 0 ==> ~(is_white x s.heap) /\ s'.heap == s.heap /\ work_at s' i == work_at s i)

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let take_keeps (cs: list nat) (g: heap) (s s': state) (i: nat) (x: obj_addr) (rest: list obj_addr)
    (out: nat{out <= 1}) (d: obj_addr)
  : Lemma (requires take_rel cs g s s' i x rest out /\ owner cs x == i)
          (ensures (~(is_white d s.heap) ==> ~(is_white d s'.heap)) /\
                   (is_black d s'.heap ==> is_black d s.heap) /\
                   ~(is_white x s'.heap) /\
                   (pending cs s d ==> pending cs s' d \/ ~(is_white d s'.heap)) /\
                   (forall (j: nat). unscanned cs s d j ==> unscanned cs s' d j))
  = if out = 1 then begin
      makeGray_eq x s.heap; makeGray_is_gray x s.heap;
      colors x s'.heap; colors x s.heap; colors d s.heap;
      if d <> x then Own.other_color s.heap x d Gray
    end;
    if owner cs d = i && L.memP d (inbox_at s i) && d <> x then
      assert (L.memP d (inbox_at s' i))
#pop-options

let take_pre (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (i: nat)
    (x: obj_addr) (rest: list obj_addr) (out: nat{out <= 1}) : prop =
  inv_mark cs g roots s /\ take_rel cs g s s' i x rest out /\ Seq.mem x (objs g) /\ owner cs x == i

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let take_grey (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (i: nat)
    (x: obj_addr) (rest: list obj_addr) (out: nat{out <= 1})
  : Lemma (requires take_pre cs g roots s s' i x rest out) (ensures grey_ok cs g s')
  = reveal_opaque (`%grey_ok) (grey_ok cs g s);
    reveal_opaque (`%grey_ok) (grey_ok cs g s');
    if out = 1 then begin
      makeGray_eq x s.heap; makeGray_is_gray x s.heap;
      others_keep s.heap x Gray
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let take_sound (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (i: nat)
    (x: obj_addr) (rest: list obj_addr) (out: nat{out <= 1})
  : Lemma (requires take_pre cs g roots s s' i x rest out) (ensures sound cs g roots s')
  = reveal_opaque (`%sound) (sound cs g roots s);
    reveal_opaque (`%sound) (sound cs g roots s');
    assert (L.memP x (inbox_at s i));
    assert (reachable g roots x);
    let inb (k: nat) (y: obj_addr) : Lemma (requires L.memP y (inbox_at s' k)) (ensures L.memP y (inbox_at s k)) =
      if k = i then () else () in
    FStar.Classical.forall_intro_2 (fun k y -> FStar.Classical.move_requires (inb k) y);
    if out = 1 then begin
      makeGray_eq x s.heap; makeGray_is_gray x s.heap;
      others_keep s.heap x Gray;
      colors x s'.heap
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let take_roots (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (i: nat)
    (x: obj_addr) (rest: list obj_addr) (out: nat{out <= 1})
  : Lemma (requires take_pre cs g roots s s' i x rest out) (ensures roots_ok cs g roots s')
  = reveal_opaque (`%roots_ok) (roots_ok cs g roots s);
    reveal_opaque (`%roots_ok) (roots_ok cs g roots s');
    FStar.Classical.forall_intro (FStar.Classical.move_requires (take_keeps cs g s s' i x rest out))
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let take_black (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (i: nat)
    (x: obj_addr) (rest: list obj_addr) (out: nat{out <= 1})
  : Lemma (requires take_pre cs g roots s s' i x rest out) (ensures black_ok cs g s')
  = reveal_opaque (`%black_ok) (black_ok cs g s');
    let blk (y: obj_addr) (j: U64.t{U64.v j >= 1})
      : Lemma (requires is_field g y j /\ is_black y s'.heap)
              (ensures ~(is_white (field_target g y j) s'.heap) \/ pending cs s' (field_target g y j) \/
                       unscanned cs s' y (U64.v j))
      = take_keeps cs g s s' i x rest out y;
        take_keeps cs g s s' i x rest out (field_target g y j);
        black_ok_at cs g s y j
    in
    FStar.Classical.forall_intro_2 (fun y j -> FStar.Classical.move_requires (blk y) j)
#pop-options

let take_mark (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (i: nat)
    (x: obj_addr) (rest: list obj_addr) (out: nat{out <= 1})
  : Lemma (requires take_pre cs g roots s s' i x rest out)
          (ensures grey_ok cs g s' /\ sound cs g roots s' /\ roots_ok cs g roots s' /\ black_ok cs g s')
  = take_grey cs g roots s s' i x rest out;
    take_sound cs g roots s s' i x rest out;
    take_roots cs g roots s s' i x rest out;
    take_black cs g roots s s' i x rest out

/// ---------------------------------------------------------------------------
/// Deliver
/// ---------------------------------------------------------------------------

let rec memP_remove_nth_or (#a: Type) (l: list a) (j: nat) (x: a)
  : Lemma (requires L.memP x l)
          (ensures L.memP x (remove_nth l j) \/ nth l j == Some x)
          (decreases l)
  = match l with
    | [] -> ()
    | y :: r ->
      if j = 0 then ()
      else FStar.Classical.or_elim #(x == y) #(L.memP x r) #(fun _ -> L.memP x (remove_nth l j) \/ nth l j == Some x)
             (fun _ -> ()) (fun _ -> memP_remove_nth_or r (j - 1) x)

/// s' is s after message jn, m, reaches its range's inbox.
let deliver_rel (cs: list nat) (g: heap) (s s': state) (jn: nat) (m: msg) : prop =
  nth s.net jn == Some m /\ owner cs m.addr == m.dest /\
  s'.heap == s.heap /\ s'.net == remove_nth s.net jn /\
  inbox_at s' m.dest == inbox_at s m.dest @ [m.addr] /\
  (forall (k: nat). k <> m.dest ==> inbox_at s' k == inbox_at s k) /\
  (forall (k: nat). work_at s' k == work_at s k /\ scan_at s' k == scan_at s k)

#push-options "--z3rlimit 20 --fuel 1 --ifuel 1"
let deliver_keeps (cs: list nat) (g: heap) (s s': state) (jn: nat) (m: msg) (d: obj_addr)
  : Lemma (requires deliver_rel cs g s s' jn m)
          (ensures pending cs s d ==> pending cs s' d)
  = let pd () : Lemma (requires pending cs s d) (ensures pending cs s' d) =
      if L.memP d (inbox_at s (owner cs d)) then
        L.append_memP (inbox_at s m.dest) [m.addr] d
      else begin
        let m' = FStar.IndefiniteDescription.indefinite_description_ghost msg
                   (fun m' -> L.memP m' s.net /\ m'.addr == d) in
        memP_remove_nth_or s.net jn m';
        if nth s.net jn = Some m' then
          L.append_memP (inbox_at s m.dest) [m.addr] d
      end
    in
    FStar.Classical.move_requires pd ()
#pop-options

let inbox_append_reach (g: heap) (roots: list obj_addr) (l: list obj_addr) (a y: obj_addr)
  : Lemma (requires (forall (z: obj_addr). L.memP z l ==> reachable g roots z) /\
                    reachable g roots a /\ L.memP y (l @ [a]))
          (ensures reachable g roots y)
  = L.append_memP l [a] y

let deliver_pre (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (jn: nat) (m: msg) : prop =
  inv_mark cs g roots s /\ deliver_rel cs g s s' jn m

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let deliver_grey (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (jn: nat) (m: msg)
  : Lemma (requires deliver_pre cs g roots s s' jn m) (ensures grey_ok cs g s')
  = reveal_opaque (`%grey_ok) (grey_ok cs g s);
    reveal_opaque (`%grey_ok) (grey_ok cs g s')
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let deliver_sound (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (jn: nat) (m: msg)
  : Lemma (requires deliver_pre cs g roots s s' jn m) (ensures sound cs g roots s')
  = reveal_opaque (`%sound) (sound cs g roots s);
    reveal_opaque (`%sound) (sound cs g roots s');
    Own.nth_memP s.net jn m;
    assert (reachable g roots m.addr);
    let inb (k: nat) (y: obj_addr)
      : Lemma (requires L.memP y (inbox_at s' k)) (ensures reachable g roots y)
      = if k = m.dest then begin
          assert (forall (z: obj_addr). L.memP z (inbox_at s m.dest) ==> reachable g roots z);
          inbox_append_reach g roots (inbox_at s m.dest) m.addr y
        end
    in
    FStar.Classical.forall_intro_2 (fun k y -> FStar.Classical.move_requires (inb k) y);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (Own.memP_remove_nth s.net jn))
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let deliver_roots (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (jn: nat) (m: msg)
  : Lemma (requires deliver_pre cs g roots s s' jn m) (ensures roots_ok cs g roots s')
  = reveal_opaque (`%roots_ok) (roots_ok cs g roots s);
    reveal_opaque (`%roots_ok) (roots_ok cs g roots s');
    FStar.Classical.forall_intro (deliver_keeps cs g s s' jn m)
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let deliver_black (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (jn: nat) (m: msg)
  : Lemma (requires deliver_pre cs g roots s s' jn m) (ensures black_ok cs g s')
  = reveal_opaque (`%black_ok) (black_ok cs g s');
    let blk (y: obj_addr) (j: U64.t{U64.v j >= 1})
      : Lemma (requires is_field g y j /\ is_black y s'.heap)
              (ensures ~(is_white (field_target g y j) s'.heap) \/ pending cs s' (field_target g y j) \/
                       unscanned cs s' y (U64.v j))
      = black_ok_at cs g s y j;
        deliver_keeps cs g s s' jn m (field_target g y j)
    in
    FStar.Classical.forall_intro_2 (fun y j -> FStar.Classical.move_requires (blk y) j)
#pop-options

let deliver_mark (cs: list nat) (g: heap) (roots: list obj_addr) (s s': state) (jn: nat) (m: msg)
  : Lemma (requires deliver_pre cs g roots s s' jn m)
          (ensures grey_ok cs g s' /\ sound cs g roots s' /\ roots_ok cs g roots s' /\ black_ok cs g s')
  = deliver_grey cs g roots s s' jn m;
    deliver_sound cs g roots s s' jn m;
    deliver_roots cs g roots s s' jn m;
    deliver_black cs g roots s s' jn m

/// ---------------------------------------------------------------------------
/// The step function meets the relations
/// ---------------------------------------------------------------------------

let accessors_upd (s: state) (i: nat) (w: worker) (s': state)
  : Lemma (requires i < L.length s.workers /\ s'.workers == set_nth s.workers i w)
          (ensures (forall (j: nat). inbox_at s' j == (if j = i then w.inbox else inbox_at s j)) /\
                   (forall (j: nat). work_at s' j == (if j = i then w.work else work_at s j)) /\
                   (forall (j: nat). scan_at s' j == (if j = i then w.scan else scan_at s j)))
  = FStar.Classical.forall_intro (Own.upd_worker s i w)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let step_pop_rel (cs: list nat) (g: heap) (s: state) (i: nat) (w: worker) (x: obj_addr) (rest: list obj_addr)
  : Lemma (requires own cs g s /\ nth s.workers i == Some w /\ w.scan == None /\ w.work == x :: rest)
          (ensures pop_rel cs g s (step cs s (Pop i)) i x rest (Own.pop_worker s w x rest).scan)
  = reveal_opaque (`%own) (own cs g s);
    Own.nth_lt s.workers i;
    let s' = step cs s (Pop i) in
    assert (s' == { s with heap = makeBlack_x x s.heap; workers = set_nth s.workers i (Own.pop_worker s w x rest) });
    accessors_upd s i (Own.pop_worker s w x rest) s';
    makeBlack_eq x s.heap;
    pop_x cs g s i x rest;
    recoloured_wosize g s.heap x;
    recoloured_no_scan g s.heap x
#pop-options

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let step_scan_rel (cs: list nat) (g: heap) (s: state) (i: nat) (w: worker) (sc: scanning)
  : Lemma (requires own cs g s /\ nth s.workers i == Some w /\ w.scan == Some sc)
          (ensures exists (out: nat{out <= 2}). scan_rel cs g s (step cs s (Scan i)) i sc out)
  = reveal_opaque (`%own) (own cs g s);
    Own.nth_lt s.workers i;
    scan_x cs g s i sc;
    let x = sc.sobj in
    let s' = step cs s (Scan i) in
    let w0 = { w with scan = next_field sc } in
    let v = get_field_x s.heap x sc.snext in
    assert (v == HeapGraph.get_field g x sc.snext);
    if HeapGraph.is_pointer_field v then begin
      HeapGraph.is_pointer_field_is_obj_addr v;
      let c = resolve_x v s.heap in
      assert (c == field_target g x sc.snext);
      assert (is_field g x sc.snext);
      if owner cs c = i then begin
        if is_white c s.heap then begin
          let w' = { w0 with work = c :: w0.work } in
          assert (s' == { s with heap = makeGray_x c s.heap; workers = set_nth s.workers i w' });
          accessors_upd s i w' s';
          makeGray_eq c s.heap;
          assert (scan_rel cs g s s' i sc 1)
        end else begin
          assert (s' == { s with workers = set_nth s.workers i w0 });
          accessors_upd s i w0 s';
          assert (scan_rel cs g s s' i sc 0)
        end
      end else begin
        assert (s' == { s with workers = set_nth s.workers i w0;
                               net = s.net @ [{ dest = owner cs c; addr = c }] });
        accessors_upd s i w0 s';
        assert (scan_rel cs g s s' i sc 2)
      end
    end else begin
      assert (s' == { s with workers = set_nth s.workers i w0 });
      accessors_upd s i w0 s';
      assert (~(is_field g x sc.snext));
      assert (scan_rel cs g s s' i sc 0)
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let step_take_rel (cs: list nat) (g: heap) (s: state) (i: nat) (w: worker) (x: obj_addr) (rest: list obj_addr)
  : Lemma (requires own cs g s /\ nth s.workers i == Some w /\ w.inbox == x :: rest)
          (ensures Seq.mem x (objs g) /\ owner cs x == i /\
                   (exists (out: nat{out <= 1}). take_rel cs g s (step cs s (Take i)) i x rest out))
  = reveal_opaque (`%own) (own cs g s);
    Own.nth_lt s.workers i;
    assert (Own.worker_ok cs g s.heap i w);
    assert (L.memP x w.inbox);
    let s' = step cs s (Take i) in
    let w0 = { w with inbox = rest } in
    if is_white x s.heap then begin
      let w' = { w0 with work = x :: w0.work } in
      assert (s' == { s with heap = makeGray_x x s.heap; workers = set_nth s.workers i w' });
      accessors_upd s i w' s';
      makeGray_eq x s.heap;
      assert (take_rel cs g s s' i x rest 1)
    end else begin
      assert (s' == { s with workers = set_nth s.workers i w0 });
      accessors_upd s i w0 s';
      assert (take_rel cs g s s' i x rest 0)
    end
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let step_deliver_rel (cs: list nat) (g: heap) (s: state) (jn: nat) (m: msg) (w: worker)
  : Lemma (requires own cs g s /\ nth s.net jn == Some m /\ nth s.workers m.dest == Some w)
          (ensures deliver_rel cs g s (step cs s (Deliver jn)) jn m)
  = reveal_opaque (`%own) (own cs g s);
    Own.nth_lt s.workers m.dest;
    Own.nth_memP s.net jn m;
    assert (Own.msg_ok cs g m);
    let s' = step cs s (Deliver jn) in
    let w' = { w with inbox = w.inbox @ [m.addr] } in
    assert (s' == { s with workers = set_nth s.workers m.dest w'; net = remove_nth s.net jn });
    accessors_upd s m.dest w' s'
#pop-options

/// ---------------------------------------------------------------------------
/// Every step keeps the invariant
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let step_mark (cs: list nat) (g: heap) (roots: list obj_addr) (s: state) (e: event)
  : Lemma (requires ctx cs g roots /\ inv_mark cs g roots s)
          (ensures inv_mark cs g roots (step cs s e))
  = let s' = step cs s e in
    reveal_opaque (`%own) (own cs g s);
    reveal_opaque (`%own) (own cs g s');
    Own.step_own cs g s e;
    match e with
    | Pop i ->
      (match nth s.workers i with
       | Some w ->
         (match w.scan, w.work with
          | None, x :: rest ->
            step_pop_rel cs g s i w x rest;
            let sc' = (Own.pop_worker s w x rest).scan in
            pop_grey cs g roots s s' i x rest sc';
            pop_sound cs g roots s s' i x rest sc';
            pop_black cs g roots s s' i x rest sc'
          | _ -> ())
       | None -> ())
    | Scan i ->
      (match nth s.workers i with
       | Some w ->
         (match w.scan with
          | Some sc ->
            step_scan_rel cs g s i w sc;
            let out = FStar.IndefiniteDescription.indefinite_description_ghost (out: nat{out <= 2})
                        (fun out -> scan_rel cs g s s' i sc out) in
            scan_grey cs g roots s s' i sc out;
            scan_sound cs g roots s s' i sc out;
            scan_black cs g roots s s' i sc out
          | None -> ())
       | None -> ())
    | Take i ->
      (match nth s.workers i with
       | Some w ->
         (match w.inbox with
          | x :: rest ->
            step_take_rel cs g s i w x rest;
            let out = FStar.IndefiniteDescription.indefinite_description_ghost (out: nat{out <= 1})
                        (fun out -> take_rel cs g s s' i x rest out) in
            take_mark cs g roots s s' i x rest out
          | [] -> ())
       | None -> ())
    | Deliver jn ->
      (match nth s.net jn with
       | Some m ->
         (match nth s.workers m.dest with
          | Some w ->
            step_deliver_rel cs g s jn m w;
            deliver_mark cs g roots s s' jn m
          | None -> ())
       | None -> ())
#pop-options

let rec run_from_mark (cs: list nat) (g: heap) (roots: list obj_addr) (s: state) (sched: list event)
  : Lemma (requires ctx cs g roots /\ inv_mark cs g roots s)
          (ensures inv_mark cs g roots (run_from cs s sched))
          (decreases sched)
  = match sched with
    | [] -> ()
    | e :: rest -> step_mark cs g roots s e; run_from_mark cs g roots (step cs s e) rest

let run_mark (cs: list nat) (g: heap) (roots: list obj_addr) (sched: list event)
  : Lemma (requires ctx cs g roots)
          (ensures inv_mark cs g roots (run cs g roots sched))
  = init_mark cs g roots;
    run_from_mark cs g roots (init cs g roots) sched
