/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.Fix — the main thread's step keeps the invariant
///
/// `main_step` runs when every worker has stopped, so the counter is 0 and
/// every stack and inbox is empty.  With no flag set, marking is done and
/// nothing else changes.  Otherwise the fix-up walks the objects in address
/// order.  The walk keeps, with r the objects still to visit:
///   wbase   the records are stopped, with empty inboxes, clear flags and
///           well-formed stacks; fn counts the stack entries; fom implies
///           fn >= 1 (a stack was full, and S >= 1); grey and black objects
///           are reachable; root objects are not white;
///   wvis    r is sorted and holds every object above lo; a visited grey
///           object is on its owner's stack, or fom is set; a stack entry
///           has been visited; a visited black object has no white child.
/// At the end every object has been visited, which is what the invariant
/// asks of the next round.  This is where fix-up step 4's rule matters: a
/// white child below the walk's position is pushed at once, one above it is
/// still to be visited and is pushed by step 3.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.Fix

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
module St = GC.Spec.MarkPar2.Step

/// ---------------------------------------------------------------------------
/// The walk's invariant
/// ---------------------------------------------------------------------------

let fwk (f: fx) (i: nat) : option wk = M1.nth f.fws i

let fstack (f: fx) (i: nat) : list obj_addr =
  match fwk f i with Some w -> w.stack | None -> []

let wrec_ok (k: cfg) (g h: heap) (i: nat) (w: wk) : prop =
  w.inbox == [] /\ w.pc == Stopped /\ w.ovf == false /\ stack_ok k g h i w.stack

[@@"opaque_to_smt"]
let wbase (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) : prop =
  L.length f.fws == nr k /\ recoloured g f.fh /\
  (forall (i: nat) (w: wk). fwk f i == Some w ==> wrec_ok k g f.fh i w) /\
  f.fn == counted f.fws /\ (f.fom ==> f.fn >= 1) /\
  (forall (x: obj_addr). Seq.mem x (objs g) /\ (is_gray x f.fh \/ is_black x f.fh) ==>
     M1.reachable g roots x) /\
  (forall (r: obj_addr). L.memP r (M1.root_objs g roots) ==> ~(is_white r f.fh))

[@@"opaque_to_smt"]
let wvis (k: cfg) (g: heap) (f: fx) (r: list obj_addr) (lo: int) : prop =
  LS.above lo r /\
  (forall (z: obj_addr). L.memP z r ==> Seq.mem z (objs g)) /\
  (forall (z: obj_addr). Seq.mem z (objs g) /\ lo < U64.v z ==> L.memP z r) /\
  (forall (x: obj_addr). Seq.mem x (objs g) /\ is_gray x f.fh /\ ~(L.memP x r) ==>
     L.memP x (fstack f (own k x)) \/ f.fom) /\
  (forall (i: nat) (x: obj_addr). L.memP x (fstack f i) ==> ~(L.memP x r)) /\
  (forall (x: obj_addr) (j: U64.t{U64.v j >= 1}).
     ~(L.memP x r) /\ I1.is_field g x j /\ is_black x f.fh ==>
     ~(is_white (I1.field_target g x j) f.fh))

let wbase_heap (k: cfg) (g: heap) (roots: list obj_addr) (f: fx)
  : Lemma (requires wbase k g roots f) (ensures recoloured g f.fh)
  = reveal_opaque (`%wbase) (wbase k g roots f)

/// One record of the walk.
let wbase_at (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (i: nat) (w: wk)
  : Lemma (requires wbase k g roots f /\ M1.nth f.fws i == Some w) (ensures wrec_ok k g f.fh i w)
  = reveal_opaque (`%wbase) (wbase k g roots f);
    assert (fwk f i == Some w)

/// How the heap moves during the walk: only white objects turn grey.
let grows (f f': fx) : prop =
  (forall (x: obj_addr). ~(is_white x f.fh) ==> ~(is_white x f'.fh)) /\
  (forall (x: obj_addr). is_black x f'.fh <==> is_black x f.fh) /\
  (forall (x: obj_addr). is_gray x f.fh ==> is_gray x f'.fh) /\
  (forall (i: nat) (x: obj_addr). L.memP x (fstack f i) ==> L.memP x (fstack f' i)) /\
  (f.fom ==> f'.fom)

let grows_refl (f: fx) : Lemma (grows f f) = ()

let grows_trans (f1 f2 f3: fx)
  : Lemma (requires grows f1 f2 /\ grows f2 f3) (ensures grows f1 f3)
  = ()

/// ---------------------------------------------------------------------------
/// Pushing on the owner's stack
/// ---------------------------------------------------------------------------

let push_shape (k: cfg) (f: fx) (x: obj_addr) (f': fx) : prop =
  f'.fh == f.fh /\ L.length f'.fws == L.length f.fws /\
  (forall (i: nat). i <> own k x ==> fwk f' i == fwk f i) /\
  (match fwk f (own k x) with
   | Some w ->
     (L.length w.stack >= k.cap_s /\ f'.fom == true /\ f'.fn == f.fn /\ fwk f' (own k x) == Some w) \/
     (L.length w.stack < k.cap_s /\ f'.fom == f.fom /\ f'.fn == f.fn + 1 /\
      fwk f' (own k x) == Some { w with stack = x :: w.stack })
   | None -> False)

let push_facts (k: cfg) (f: fx) (x: obj_addr)
  : Lemma (requires own k x < L.length f.fws)
          (ensures push_shape k f x (push_fx k f x))
  = Own.nth_lt f.fws (own k x);
    let Some w = M1.nth f.fws (own k x) in
    if L.length w.stack >= k.cap_s then ()
    else FStar.Classical.forall_intro (LS.nth_upd f.fws (own k x) { w with stack = x :: w.stack })

/// The pushed record is well formed.
let push_rec (k: cfg) (g: heap) (f: fx) (x: obj_addr) (w: wk)
  : Lemma (requires wrec_ok k g f.fh (own k x) w /\ ~(L.memP x w.stack) /\ Seq.mem x (objs g) /\
                    is_gray x f.fh)
          (ensures wrec_ok k g f.fh (own k x) { w with stack = x :: w.stack })
  = ()

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let push_full (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (x: obj_addr) (w: wk)
  : Lemma (requires wbase k g roots f /\ k.cap_s >= 1 /\ fwk f (own k x) == Some w /\
                    L.length w.stack >= k.cap_s /\ push_shape k f x (push_fx k f x))
          (ensures (let f' = push_fx k f x in wbase k g roots f' /\ grows f f' /\ f'.fom /\
                    (forall (i: nat). fstack f' i == fstack f i)))
  = reveal_opaque (`%wbase) (wbase k g roots f);
    reveal_opaque (`%wbase) (wbase k g roots (push_fx k f x));
    LS.counted_ge f.fws (own k x)
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let push_room (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (x: obj_addr) (w: wk)
  : Lemma (requires wbase k g roots f /\ fwk f (own k x) == Some w /\ Seq.mem x (objs g) /\
                    is_gray x f.fh /\ ~(L.memP x w.stack) /\
                    L.length w.stack < k.cap_s /\ push_shape k f x (push_fx k f x))
          (ensures (let f' = push_fx k f x in wbase k g roots f' /\ grows f f' /\
                    L.memP x (fstack f' (own k x)) /\
                    (forall (i: nat) (z: obj_addr). L.memP z (fstack f' i) ==>
                       L.memP z (fstack f i) \/ z == x)))
  = let f' = push_fx k f x in
    reveal_opaque (`%wbase) (wbase k g roots f);
    reveal_opaque (`%wbase) (wbase k g roots f');
    push_rec k g f x w;
    LS.counted_set f.fws (own k x) { w with stack = x :: w.stack }
#pop-options

let push_base (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (x: obj_addr)
  : Lemma (requires wbase k g roots f /\ k.cap_s >= 1 /\ Seq.mem x (objs g) /\ is_gray x f.fh /\
                    (forall (i: nat). ~(L.memP x (fstack f i))))
          (ensures (let f' = push_fx k f x in
                    wbase k g roots f' /\ grows f f' /\
                    (L.memP x (fstack f' (own k x)) \/ f'.fom) /\
                    (forall (i: nat) (z: obj_addr). L.memP z (fstack f' i) ==>
                       L.memP z (fstack f i) \/ z == x)))
  = reveal_opaque (`%wbase) (wbase k g roots f);
    own_lt k x;
    push_facts k f x;
    Own.nth_lt f.fws (own k x);
    let Some w = M1.nth f.fws (own k x) in
    assert (fstack f (own k x) == w.stack);
    if L.length w.stack >= k.cap_s then push_full k g roots f x w
    else push_room k g roots f x w

/// ---------------------------------------------------------------------------
/// Greying a white child
/// ---------------------------------------------------------------------------

/// A stopped record survives greying a white object.
let wrec_recolour (k: cfg) (g h: heap) (i: nat) (w: wk) (c: obj_addr)
  : Lemma (requires wrec_ok k g h i w /\ is_white c h)
          (ensures wrec_ok k g (set_object_color c h Gray) i w /\ ~(L.memP c w.stack))
  = colors c h;
    let aux (y: obj_addr) : Lemma (requires L.memP y w.stack) (ensures is_gray y (set_object_color c h Gray)) =
      colors y h; Own.other_color h c y Gray in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let white_unstacked (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (c: obj_addr)
  : Lemma (requires wbase k g roots f /\ is_white c f.fh)
          (ensures forall (i: nat). ~(L.memP c (fstack f i)))
  = reveal_opaque (`%wbase) (wbase k g roots f);
    colors c f.fh;
    let aux (i: nat) : Lemma (~(L.memP c (fstack f i))) =
      match fwk f i with
      | Some w -> assert (wrec_ok k g f.fh i w); assert (stack_ok k g f.fh i w.stack)
      | None -> ()
    in
    FStar.Classical.forall_intro aux

let grey_colors (f: fx) (c: obj_addr)
  : Lemma (requires is_white c f.fh /\ ~(is_blue c f.fh))
          (ensures (let h' = makeGray_x c f.fh in
                    h' == set_object_color c f.fh Gray /\ is_gray c h' /\
                    (forall (x: obj_addr). x <> c ==>
                       is_gray x h' == is_gray x f.fh /\ is_white x h' == is_white x f.fh /\
                       is_black x h' == is_black x f.fh) /\
                    (forall (x: obj_addr). ~(is_white x f.fh) ==> ~(is_white x h')) /\
                    (forall (x: obj_addr). is_black x h' <==> is_black x f.fh) /\
                    (forall (x: obj_addr). is_gray x f.fh ==> is_gray x h')))
  = makeGray_eq c f.fh;
    makeGray_is_gray c f.fh;
    I1.others_keep f.fh c Gray;
    colors c f.fh; colors c (makeGray_x c f.fh)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let grey_wbase (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (c: obj_addr)
  : Lemma (requires wbase k g roots f /\ Seq.mem c (objs g) /\ is_white c f.fh /\
                    ~(is_blue c g) /\ M1.reachable g roots c)
          (ensures wbase k g roots { f with fh = makeGray_x c f.fh })
  = reveal_opaque (`%wbase) (wbase k g roots f);
    let h' = makeGray_x c f.fh in
    reveal_opaque (`%wbase) (wbase k g roots { f with fh = h' });
    recoloured_blue g f.fh c;
    grey_colors f c;
    recoloured_makeGray g f.fh c;
    let rec_ok (i: nat) (w: wk)
      : Lemma (requires fwk f i == Some w) (ensures wrec_ok k g h' i w)
      = wrec_recolour k g f.fh i w c
    in
    FStar.Classical.forall_intro_2 (fun i w -> FStar.Classical.move_requires (rec_ok i) w)
#pop-options

let grey_base (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (c: obj_addr)
  : Lemma (requires wbase k g roots f /\ Seq.mem c (objs g) /\ is_white c f.fh /\
                    ~(is_blue c g) /\ M1.reachable g roots c)
          (ensures (let f' = { f with fh = makeGray_x c f.fh } in
                    wbase k g roots f' /\ grows f f' /\ is_gray c f'.fh /\
                    (forall (i: nat). ~(L.memP c (fstack f i))) /\
                    (forall (x: obj_addr). x <> c ==>
                       is_gray x f'.fh == is_gray x f.fh /\ is_white x f'.fh == is_white x f.fh)))
  = reveal_opaque (`%wbase) (wbase k g roots f);
    recoloured_blue g f.fh c;
    grey_colors f c;
    white_unstacked k g roots f c;
    grey_wbase k g roots f c

/// ---------------------------------------------------------------------------
/// One field of the black object y at the walk's position
/// ---------------------------------------------------------------------------

/// The facts about y the field loop uses.
let at_y (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (y: obj_addr) (rest: list obj_addr)
    (lo: int) : prop =
  ctx k g roots /\ wbase k g roots f /\ wvis k g f (y :: rest) lo /\
  Seq.mem y (objs g) /\ is_black y f.fh /\ ~(is_no_scan y g)

/// The field read in the current heap is g's.
let field_now (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (y: obj_addr)
    (j: U64.t{U64.v j >= 1})
  : Lemma (requires wbase k g roots f /\ Seq.mem y (objs g) /\ U64.v j <= U64.v (wosize_of_object y g))
          (ensures get_field_x f.fh y j == HeapGraph.get_field g y j /\
                   wosize_x y f.fh == wosize_of_object y g)
  = reveal_opaque (`%wbase) (wbase k g roots f);
    recoloured_wosize g f.fh y

/// The target of a pointer field of y: enumerated, non-blue, reachable,
/// resolved in the current heap as in g.
let child_facts (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (y: obj_addr) (rest: list obj_addr)
    (lo: int) (j: U64.t{U64.v j >= 1})
  : Lemma (requires at_y k g roots f y rest lo /\ I1.is_field g y j)
          (ensures (let c = I1.field_target g y j in
                    let v = HeapGraph.get_field g y j in
                    HeapGraph.is_pointer_field v /\
                    (HeapGraph.is_pointer_field_is_obj_addr v; resolve_x (v <: obj_addr) f.fh == c) /\
                    Seq.mem c (objs g) /\ ~(is_blue c g) /\ M1.reachable g roots c))
  = reveal_opaque (`%wbase) (wbase k g roots f);
    reveal_opaque (`%ctx) (ctx k g roots);
    reveal_opaque (`%I1.ctx) (I1.ctx k.cs g roots);
    I1.target_facts k.cs g roots y j

/// Pushing a greyed child below y keeps wvis: it is not in y :: rest.
let below_not_in (y: obj_addr) (rest: list obj_addr) (lo: int) (c: obj_addr)
  : Lemma (requires LS.above lo (y :: rest) /\ U64.v c < U64.v y) (ensures ~(L.memP c (y :: rest)))
  = FStar.Classical.move_requires (LS.above_mem (U64.v y) rest) c

/// A greyed child above y is still to be visited.
let above_in (k: cfg) (g: heap) (f: fx) (y: obj_addr) (rest: list obj_addr) (lo: int) (c: obj_addr)
  : Lemma (requires wvis k g f (y :: rest) lo /\ Seq.mem c (objs g) /\ U64.v c >= U64.v y /\ c <> y)
          (ensures L.memP c (y :: rest))
  = reveal_opaque (`%wvis) (wvis k g f (y :: rest) lo)

/// wvis carries over a step that only greys and pushes, given that every
/// newly grey object is on its owner's stack, still to be visited, or
/// fom is set, and every new stack entry is not in r.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let wvis_grows (k: cfg) (g: heap) (f f': fx) (r: list obj_addr) (lo: int)
  : Lemma (requires wvis k g f r lo /\ grows f f' /\
                    (forall (x: obj_addr). Seq.mem x (objs g) /\ is_gray x f'.fh /\ ~(is_gray x f.fh) ==>
                       L.memP x r \/ L.memP x (fstack f' (own k x)) \/ f'.fom) /\
                    (forall (i: nat) (z: obj_addr). L.memP z (fstack f' i) ==>
                       L.memP z (fstack f i) \/ ~(L.memP z r)))
          (ensures wvis k g f' r lo)
  = reveal_opaque (`%wvis) (wvis k g f r lo);
    reveal_opaque (`%wvis) (wvis k g f' r lo)
#pop-options

/// fix_child on a pointer to a white object, unfolded.
let fix_child_white (k: cfg) (y: obj_addr) (f: fx) (v: U64.t) (c: obj_addr)
  : Lemma (requires HeapGraph.is_pointer_field v /\
                    (HeapGraph.is_pointer_field_is_obj_addr v; resolve_x (v <: obj_addr) f.fh == c) /\
                    is_white c f.fh)
          (ensures fix_child k y f v ==
                   (let f1 = { f with fh = makeGray_x c f.fh } in
                    if U64.v c < U64.v y then push_fx k f1 c else f1))
  = HeapGraph.is_pointer_field_is_obj_addr v

/// Greying, and pushing, a white child below y.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let child_below (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (y: obj_addr)
    (rest: list obj_addr) (lo: int) (c: obj_addr)
  : Lemma (requires ctx k g roots /\ wbase k g roots f /\ wvis k g f (y :: rest) lo /\
                    Seq.mem c (objs g) /\ is_white c f.fh /\ ~(is_blue c g) /\
                    M1.reachable g roots c /\ U64.v c < U64.v y)
          (ensures (let f2 = push_fx k { f with fh = makeGray_x c f.fh } c in
                    wbase k g roots f2 /\ wvis k g f2 (y :: rest) lo /\ grows f f2 /\
                    ~(is_white c f2.fh)))
  = ctx_elim k g roots;
    let f1 = { f with fh = makeGray_x c f.fh } in
    grey_base k g roots f c;
    push_base k g roots f1 c;
    let f2 = push_fx k f1 c in
    reveal_opaque (`%wvis) (wvis k g f (y :: rest) lo);
    below_not_in y rest lo c;
    colors c f1.fh;
    grows_trans f f1 f2;
    wvis_grows k g f f2 (y :: rest) lo
#pop-options

/// Greying, without pushing, a white child at or above y.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let child_above (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (y: obj_addr)
    (rest: list obj_addr) (lo: int) (c: obj_addr)
  : Lemma (requires wbase k g roots f /\ wvis k g f (y :: rest) lo /\
                    Seq.mem c (objs g) /\ is_white c f.fh /\ ~(is_blue c g) /\
                    M1.reachable g roots c /\ U64.v c >= U64.v y /\ c <> y)
          (ensures (let f1 = { f with fh = makeGray_x c f.fh } in
                    wbase k g roots f1 /\ wvis k g f1 (y :: rest) lo /\ grows f f1 /\
                    ~(is_white c f1.fh)))
  = let f1 = { f with fh = makeGray_x c f.fh } in
    grey_base k g roots f c;
    above_in k g f y rest lo c;
    colors c f1.fh;
    wvis_grows k g f f1 (y :: rest) lo
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let child_white (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (y: obj_addr)
    (rest: list obj_addr) (lo: int) (j: U64.t{U64.v j >= 1})
  : Lemma (requires at_y k g roots f y rest lo /\ I1.is_field g y j /\
                    is_white (I1.field_target g y j) f.fh)
          (ensures (let f' = fix_child k y f (get_field_x f.fh y j) in
                    wbase k g roots f' /\ wvis k g f' (y :: rest) lo /\ grows f f' /\
                    ~(is_white (I1.field_target g y j) f'.fh)))
  = let c = I1.field_target g y j in
    child_facts k g roots f y rest lo j;
    field_now k g roots f y j;
    fix_child_white k y f (get_field_x f.fh y j) c;
    colors y f.fh; colors c f.fh;
    if U64.v c < U64.v y then child_below k g roots f y rest lo c
    else child_above k g roots f y rest lo c
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let child_step (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (y: obj_addr)
    (rest: list obj_addr) (lo: int) (j: U64.t{U64.v j >= 1})
  : Lemma (requires at_y k g roots f y rest lo /\ U64.v j <= U64.v (wosize_of_object y g))
          (ensures (let f' = fix_child k y f (get_field_x f.fh y j) in
                    wbase k g roots f' /\ wvis k g f' (y :: rest) lo /\ grows f f' /\
                    (I1.is_field g y j ==> ~(is_white (I1.field_target g y j) f'.fh))))
  = field_now k g roots f y j;
    reveal_opaque (`%wbase) (wbase k g roots f);
    let v = get_field_x f.fh y j in
    colors y f.fh;
    recoloured_blue g f.fh y;
    assert (HeapGraph.is_pointer_field v ==> I1.is_field g y j);
    if I1.is_field g y j then begin
      child_facts k g roots f y rest lo j;
      let c = I1.field_target g y j in
      if is_white_x c f.fh then child_white k g roots f y rest lo j
      else assert (fix_child k y f v == f)
    end else assert (fix_child k y f v == f)
#pop-options

/// ---------------------------------------------------------------------------
/// All fields of y
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let rec fields_step (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (y: obj_addr)
    (rest: list obj_addr) (lo: int) (j: U64.t{U64.v j >= 1}) (ws: U64.t)
  : Lemma (requires at_y k g roots f y rest lo /\ ws == wosize_of_object y g)
          (ensures (let f' = fix_fields k y j ws f in
                    wbase k g roots f' /\ wvis k g f' (y :: rest) lo /\ grows f f' /\
                    (forall (j': U64.t{U64.v j' >= 1}). U64.v j <= U64.v j' /\ I1.is_field g y j' ==>
                       ~(is_white (I1.field_target g y j') f'.fh))))
          (decreases (U64.v ws - U64.v j))
  = if U64.v j > U64.v ws then grows_refl f
    else begin
      let f1 = fix_child k y f (get_field_x f.fh y j) in
      child_step k g roots f y rest lo j;
      if U64.v j < U64.v ws then begin
        fields_step k g roots f1 y rest lo (U64.add j 1UL) ws;
        let f2 = fix_fields k y (U64.add j 1UL) ws f1 in
        grows_trans f f1 f2;
        let aux (j': U64.t{U64.v j' >= 1})
          : Lemma (requires U64.v j <= U64.v j' /\ I1.is_field g y j')
                  (ensures ~(is_white (I1.field_target g y j') f2.fh))
          = if U64.v j' = U64.v j then U64.v_inj j' j else ()
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
      end else begin
        let aux (j': U64.t{U64.v j' >= 1})
          : Lemma (requires U64.v j <= U64.v j' /\ I1.is_field g y j')
                  (ensures ~(is_white (I1.field_target g y j') f1.fh))
          = U64.v_inj j' j
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
      end
    end
#pop-options

/// ---------------------------------------------------------------------------
/// One object
/// ---------------------------------------------------------------------------

/// Moving past y: what was true of r = y :: rest at lo is true of rest at y.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let advance (k: cfg) (g: heap) (f: fx) (y: obj_addr) (rest: list obj_addr) (lo: int)
  : Lemma (requires wvis k g f (y :: rest) lo /\
                    (is_gray y f.fh ==> L.memP y (fstack f (own k y)) \/ f.fom) /\
                    (forall (i: nat). ~(L.memP y (fstack f i)) \/ ~(L.memP y rest)) /\
                    (forall (j: U64.t{U64.v j >= 1}). I1.is_field g y j /\ is_black y f.fh ==>
                       ~(is_white (I1.field_target g y j) f.fh)))
          (ensures wvis k g f rest (U64.v y))
  = reveal_opaque (`%wvis) (wvis k g f (y :: rest) lo);
    reveal_opaque (`%wvis) (wvis k g f rest (U64.v y));
    LS.above_norepeats lo (y :: rest);
    let ab (z: obj_addr) : Lemma (requires Seq.mem z (objs g) /\ U64.v y < U64.v z) (ensures L.memP z rest) =
      assert (L.memP z (y :: rest)) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires ab)
#pop-options

/// Pushing y itself and moving past it.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let advance_push (k: cfg) (g: heap) (f f': fx) (y: obj_addr) (rest: list obj_addr) (lo: int)
  : Lemma (requires wvis k g f (y :: rest) lo /\ grows f f' /\ f'.fh == f.fh /\ is_gray y f.fh /\
                    (L.memP y (fstack f' (own k y)) \/ f'.fom) /\
                    (forall (i: nat) (z: obj_addr). L.memP z (fstack f' i) ==>
                       L.memP z (fstack f i) \/ z == y))
          (ensures wvis k g f' rest (U64.v y))
  = reveal_opaque (`%wvis) (wvis k g f (y :: rest) lo);
    reveal_opaque (`%wvis) (wvis k g f' rest (U64.v y));
    LS.above_norepeats lo (y :: rest);
    colors y f.fh;
    let ab (z: obj_addr) : Lemma (requires Seq.mem z (objs g) /\ U64.v y < U64.v z) (ensures L.memP z rest) =
      assert (L.memP z (y :: rest)) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires ab)
#pop-options

let obj_pre (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (y: obj_addr) (rest: list obj_addr)
    (lo: int) : prop =
  ctx k g roots /\ wbase k g roots f /\ wvis k g f (y :: rest) lo

let obj_facts (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (y: obj_addr) (rest: list obj_addr)
    (lo: int)
  : Lemma (requires obj_pre k g roots f y rest lo)
          (ensures Seq.mem y (objs g) /\ k.cap_s >= 1 /\ L.length f.fws == nr k /\
                   (forall (i: nat). ~(L.memP y (fstack f i))) /\
                   is_no_scan_x y f.fh == is_no_scan y g /\ wosize_x y f.fh == wosize_of_object y g)
  = reveal_opaque (`%wvis) (wvis k g f (y :: rest) lo);
    reveal_opaque (`%wbase) (wbase k g roots f);
    ctx_elim k g roots;
    assert (Seq.mem y (objs g));
    recoloured_no_scan g f.fh y;
    recoloured_wosize g f.fh y

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let obj_grey (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (y: obj_addr) (rest: list obj_addr)
    (lo: int)
  : Lemma (requires obj_pre k g roots f y rest lo /\ is_gray y f.fh)
          (ensures (let f' = push_fx k f y in
                    wbase k g roots f' /\ wvis k g f' rest (U64.v y) /\ grows f f'))
  = obj_facts k g roots f y rest lo;
    own_lt k y;
    push_base k g roots f y;
    push_facts k f y;
    advance_push k g f (push_fx k f y) y rest lo
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let obj_black (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (y: obj_addr) (rest: list obj_addr)
    (lo: int)
  : Lemma (requires obj_pre k g roots f y rest lo /\ is_black y f.fh /\ ~(is_no_scan y g))
          (ensures (let f' = fix_fields k y 1UL (wosize_of_object y g) f in
                    wbase k g roots f' /\ wvis k g f' rest (U64.v y) /\ grows f f'))
  = obj_facts k g roots f y rest lo;
    fields_step k g roots f y rest lo 1UL (wosize_of_object y g);
    let f' = fix_fields k y 1UL (wosize_of_object y g) f in
    reveal_opaque (`%wvis) (wvis k g f' (y :: rest) lo);
    colors y f'.fh;
    advance k g f' y rest lo
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let obj_other (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (y: obj_addr) (rest: list obj_addr)
    (lo: int)
  : Lemma (requires obj_pre k g roots f y rest lo /\ ~(is_gray y f.fh) /\
                    ~(is_black y f.fh /\ ~(is_no_scan y g)))
          (ensures wbase k g roots f /\ wvis k g f rest (U64.v y) /\ grows f f)
  = obj_facts k g roots f y rest lo;
    grows_refl f;
    advance k g f y rest lo
#pop-options

let obj_step (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (y: obj_addr) (rest: list obj_addr)
    (lo: int)
  : Lemma (requires ctx k g roots /\ wbase k g roots f /\ wvis k g f (y :: rest) lo)
          (ensures (let f' = fix_obj k f y in
                    wbase k g roots f' /\ wvis k g f' rest (U64.v y) /\ grows f f'))
  = obj_facts k g roots f y rest lo;
    if is_gray_x y f.fh then obj_grey k g roots f y rest lo
    else if is_black_x y f.fh && not (is_no_scan_x y f.fh) then obj_black k g roots f y rest lo
    else obj_other k g roots f y rest lo

let rec walk_step (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (r: list obj_addr) (lo: int)
  : Lemma (requires ctx k g roots /\ wbase k g roots f /\ wvis k g f r lo)
          (ensures (let f' = fix_walk k f r in
                    wbase k g roots f' /\ (exists (lo': int). wvis k g f' [] lo') /\ grows f f'))
          (decreases r)
  = match r with
    | [] -> grows_refl f
    | y :: rest ->
      obj_step k g roots f y rest lo;
      walk_step k g roots (fix_obj k f y) rest (U64.v y);
      grows_trans f (fix_obj k f y) (fix_walk k (fix_obj k f y) rest)
