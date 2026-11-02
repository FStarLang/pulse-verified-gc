/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.Inv — the invariant of the Stage 3 model
///
/// In every state a run reaches (`inv`):
///   own_ok    each worker's stack holds grey objects it owns, without
///             repeats; each inbox entry, and a taken one, has its header
///             word in the worker's range and names an enumerated non-blue
///             object; a worker scanning holds a black object of its own;
///             the heap is g recoloured
///   count_ok  the counter equals the counted entries, and is 0 if any
///             worker has stopped
///   grey_ok   a grey object is on its owner's stack, or an overflow flag
///             is set
///   sound     every grey or black object, and every object an inbox entry
///             or a taken entry names, is reachable
///   roots_ok  every root object is non-white (setup greys them)
///   black_ok  for a pointer field j of a black scannable object x, the
///             object it names is non-white, or pending (some worker holds
///             an entry naming it), or x is being scanned and has not
///             reached field j, or an overflow flag is set
///   fin_ok    once marking is done, no flag is set, every worker has
///             stopped, and the counter is 0.
/// At the end, then, no object is grey, every root object is black, and no
/// black object points to a white one.
///
/// `black_ok_but s (Some c)` exempts the fields naming c: it holds in the
/// middle of a step, after the worker has read a field naming c or taken an
/// entry naming c, and before it has routed it.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.Inv

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
open GC.Spec.MarkPar.Exec
open GC.Spec.MarkPar.Recolour
open GC.Spec.MarkPar2.Model

module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark
module M1 = GC.Spec.MarkPar.Model
module I1 = GC.Spec.MarkPar.Inv

let objs (g: heap) = objects zero_addr g

/// ---------------------------------------------------------------------------
/// Accessors
/// ---------------------------------------------------------------------------

let wk_of (s: state) (i: nat) : option wk = M1.nth s.wks i

let stack_of (s: state) (i: nat) : list obj_addr =
  match wk_of s i with Some w -> w.stack | None -> []

let pc_of (s: state) (i: nat) : pc =
  match wk_of s i with Some w -> w.pc | None -> Stopped

/// Worker i holds v: in its inbox, or taken and not yet accepted.
let holds (s: state) (i: nat) (v: obj_addr) : prop =
  match wk_of s i with Some w -> L.memP v w.inbox \/ w.pc == Got v | None -> False

/// Some worker holds an entry naming c.
let pending (g: heap) (s: state) (c: obj_addr) : prop =
  exists (i: nat) (v: obj_addr). holds s i v /\ resolve_object v g == c

/// x's owner is part-way through x, at or before field j.
let unscanned (k: cfg) (s: state) (x: obj_addr) (j: nat) : prop =
  match pc_of s (own k x) with
  | Scan sc -> sc.M1.sobj == x /\ U64.v sc.M1.snext <= j
  | _ -> False

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

let entry_ok (k: cfg) (g: heap) (i: nat) (v: obj_addr) : prop =
  own k v == i /\ Seq.mem (resolve_object v g) (objs g) /\ ~(is_blue (resolve_object v g) g)

let stack_ok (k: cfg) (g h: heap) (i: nat) (l: list obj_addr) : prop =
  L.noRepeats l /\
  (forall (x: obj_addr). L.memP x l ==> Seq.mem x (objs g) /\ own k x == i /\ is_gray x h)

let pc_ok (k: cfg) (g h: heap) (i: nat) (p: pc) : prop =
  match p with
  | Scan sc ->
    Seq.mem sc.M1.sobj (objs g) /\ own k sc.M1.sobj == i /\ is_black sc.M1.sobj h /\
    ~(is_no_scan sc.M1.sobj g) /\ U64.v sc.M1.snext <= U64.v sc.M1.sws /\
    sc.M1.sws == wosize_of_object sc.M1.sobj g
  | Got v -> entry_ok k g i v
  | _ -> True

let wk_ok (k: cfg) (g h: heap) (i: nat) (w: wk) : prop =
  stack_ok k g h i w.stack /\
  (forall (v: obj_addr). L.memP v w.inbox ==> entry_ok k g i v) /\
  pc_ok k g h i w.pc

[@@"opaque_to_smt"]
let own_ok (k: cfg) (g: heap) (s: state) : prop =
  L.length s.wks == nr k /\ recoloured g s.heap /\
  (forall (i: nat) (w: wk). wk_of s i == Some w ==> wk_ok k g s.heap i w)

[@@"opaque_to_smt"]
let count_ok (s: state) : prop =
  s.count == counted s.wks /\
  (forall (i: nat) (w: wk). wk_of s i == Some w /\ Stopped? w.pc ==> s.count == 0)

[@@"opaque_to_smt"]
let grey_ok (k: cfg) (g: heap) (s: state) : prop =
  forall (x: obj_addr). Seq.mem x (objs g) /\ is_gray x s.heap ==>
    L.memP x (stack_of s (own k x)) \/ flagged s

[@@"opaque_to_smt"]
let sound (g: heap) (roots: list obj_addr) (s: state) : prop =
  (forall (x: obj_addr). Seq.mem x (objs g) /\ (is_gray x s.heap \/ is_black x s.heap) ==>
     M1.reachable g roots x) /\
  (forall (i: nat) (v: obj_addr). holds s i v ==> M1.reachable g roots (resolve_object v g))

[@@"opaque_to_smt"]
let roots_ok (g: heap) (roots: list obj_addr) (s: state) : prop =
  forall (r: obj_addr). L.memP r (M1.root_objs g roots) ==> ~(is_white r s.heap)

let covered (k: cfg) (g: heap) (s: state) (c x: obj_addr) (j: nat) : prop =
  ~(is_white c s.heap) \/ pending g s c \/ unscanned k s x j \/ flagged s

[@@"opaque_to_smt"]
let black_ok_but (k: cfg) (g: heap) (s: state) (c0: option obj_addr) : prop =
  forall (x: obj_addr) (j: U64.t{U64.v j >= 1}).
    I1.is_field g x j /\ is_black x s.heap ==>
    covered k g s (I1.field_target g x j) x (U64.v j) \/ c0 == Some (I1.field_target g x j)

let black_ok (k: cfg) (g: heap) (s: state) : prop = black_ok_but k g s None

[@@"opaque_to_smt"]
let fin_ok (s: state) : prop =
  s.finished ==> ~(flagged s) /\ all_stopped s.wks /\ s.count == 0

let core (k: cfg) (g: heap) (roots: list obj_addr) (s: state) : prop =
  own_ok k g s /\ count_ok s /\ grey_ok k g s /\ sound g roots s /\ roots_ok g roots s /\ fin_ok s

let inv (k: cfg) (g: heap) (roots: list obj_addr) (s: state) : prop =
  core k g roots s /\ black_ok k g s

/// The setting every lemma assumes.
[@@"opaque_to_smt"]
let ctx (k: cfg) (g: heap) (roots: list obj_addr) : prop =
  M1.mark_pre g roots /\ M1.graph_pre g roots /\ valid_cfg k

/// ---------------------------------------------------------------------------
/// Basic facts
/// ---------------------------------------------------------------------------

let ctx_elim (k: cfg) (g: heap) (roots: list obj_addr)
  : Lemma (requires ctx k g roots)
          (ensures M1.mark_pre g roots /\ M1.graph_pre g roots /\ valid_cfg k /\
                   well_formed_heap g /\ Mark.no_pointer_to_blue g /\ k.cap_s >= 1)
  = reveal_opaque (`%ctx) (ctx k g roots)

/// An enumerated object of a well-formed heap is not infix, so it resolves
/// to itself.
let resolve_self (g: heap) (c: obj_addr)
  : Lemma (requires well_formed_heap g /\ Seq.mem c (objs g))
          (ensures resolve_object c g == c)
  = wf_parts ();
    assert (well_formed_heap_part4 g);
    assert (Seq.mem c (objects zero_addr g));
    assert (~(is_infix c g));
    resolve_non_infix c g

/// The object an entry names is the same in a recoloured heap.
let resolve_recoloured (g h: heap) (v: obj_addr)
  : Lemma (requires recoloured g h) (ensures resolve_x v h == resolve_object v g)
  = ()

let own_lt (k: cfg) (x: obj_addr)
  : Lemma (own k x < nr k)
  = I1.count_le_lt k.cs (U64.v (hd_address x))

let colors = I1.colors

/// ---------------------------------------------------------------------------
/// Covering, kept
/// ---------------------------------------------------------------------------

/// One black_ok_but instance.
let black_ok_at (k: cfg) (g: heap) (s: state) (c0: option obj_addr)
    (x: obj_addr) (j: U64.t{U64.v j >= 1})
  : Lemma (requires black_ok_but k g s c0 /\ I1.is_field g x j /\ is_black x s.heap)
          (ensures covered k g s (I1.field_target g x j) x (U64.v j) \/
                   c0 == Some (I1.field_target g x j))
  = reveal_opaque (`%black_ok_but) (black_ok_but k g s c0)

/// What a step must keep for black_ok_but to carry over unchanged: no
/// object turns black, nothing turns white, pending entries stay pending,
/// unscanned stays unscanned, and a set flag stays set.
let keeps (k: cfg) (g: heap) (s s': state) : prop =
  (forall (x: obj_addr). is_black x s'.heap ==> is_black x s.heap) /\
  (forall (x: obj_addr). ~(is_white x s.heap) ==> ~(is_white x s'.heap)) /\
  (forall (i: nat) (v: obj_addr). holds s i v ==> holds s' i v) /\
  (forall (x: obj_addr) (j: nat). unscanned k s x j ==> unscanned k s' x j) /\
  (flagged s ==> flagged s')

let keeps_pending (k: cfg) (g: heap) (s s': state) (c: obj_addr)
  : Lemma (requires keeps k g s s' /\ pending g s c) (ensures pending g s' c)
  = ()

let black_keeps (k: cfg) (g: heap) (s s': state) (c0: option obj_addr)
  : Lemma (requires black_ok_but k g s c0 /\ keeps k g s s')
          (ensures black_ok_but k g s' c0)
  = reveal_opaque (`%black_ok_but) (black_ok_but k g s' c0);
    let aux (x: obj_addr) (j: U64.t{U64.v j >= 1})
      : Lemma (requires I1.is_field g x j /\ is_black x s'.heap)
              (ensures covered k g s' (I1.field_target g x j) x (U64.v j) \/
                       c0 == Some (I1.field_target g x j))
      = black_ok_at k g s c0 x j;
        let c = I1.field_target g x j in
        FStar.Classical.move_requires (keeps_pending k g s s') c
    in
    FStar.Classical.forall_intro_2 (fun x j -> FStar.Classical.move_requires (aux x) j)

/// Covering c0 itself turns black_ok_but (Some c0) into black_ok.
let black_cover (k: cfg) (g: heap) (s: state) (c0: obj_addr)
  : Lemma (requires black_ok_but k g s (Some c0) /\
                    (~(is_white c0 s.heap) \/ pending g s c0 \/ flagged s))
          (ensures black_ok k g s)
  = reveal_opaque (`%black_ok_but) (black_ok_but k g s None);
    let aux (x: obj_addr) (j: U64.t{U64.v j >= 1})
      : Lemma (requires I1.is_field g x j /\ is_black x s.heap)
              (ensures covered k g s (I1.field_target g x j) x (U64.v j))
      = black_ok_at k g s (Some c0) x j
    in
    FStar.Classical.forall_intro_2 (fun x j -> FStar.Classical.move_requires (aux x) j)

let black_weaken (k: cfg) (g: heap) (s: state) (c0: obj_addr)
  : Lemma (requires black_ok k g s) (ensures black_ok_but k g s (Some c0))
  = reveal_opaque (`%black_ok_but) (black_ok_but k g s None);
    reveal_opaque (`%black_ok_but) (black_ok_but k g s (Some c0))
