/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar2.Init — setup establishes the invariant
///
/// Setup darkens the roots one by one, as `check_and_darken_bounded_spec`
/// does: resolve, grey if white, push on the owner's stack or set
/// overflow_main.  Along the way (`sinv`): every record is at the top of
/// the loop with an empty inbox and a clear flag; fn counts the stack
/// entries; a grey object is on its owner's stack, or fom is set; no object
/// is black; grey objects are reachable; and every root darkened so far
/// names a non-white object.  The initial state then meets `inv`: with no
/// black object, black_ok holds trivially.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar2.Init

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
module R = GC.Spec.MarkPar.Roots
module LS = GC.Spec.MarkPar2.Lists
module U = GC.Spec.MarkPar2.Upd
module A = GC.Spec.MarkPar2.Act
module FX = GC.Spec.MarkPar2.Fix

let srec_ok (k: cfg) (g h: heap) (i: nat) (w: wk) : prop =
  w.inbox == [] /\ w.pc == Loop /\ w.ovf == false /\ stack_ok k g h i w.stack

[@@"opaque_to_smt"]
let sinv (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (done: list obj_addr) : prop =
  L.length f.fws == nr k /\ recoloured g f.fh /\
  (forall (i: nat) (w: wk). FX.fwk f i == Some w ==> srec_ok k g f.fh i w) /\
  f.fn == counted f.fws /\
  (forall (x: obj_addr). Seq.mem x (objs g) /\ is_gray x f.fh ==>
     L.memP x (FX.fstack f (own k x)) \/ f.fom) /\
  (forall (x: obj_addr). Seq.mem x (objs g) ==> ~(is_black x f.fh)) /\
  (forall (x: obj_addr). Seq.mem x (objs g) /\ is_gray x f.fh ==> M1.reachable g roots x) /\
  (forall (r: obj_addr). L.memP r done ==> ~(is_white (resolve_object r g) f.fh))

/// ---------------------------------------------------------------------------
/// The start
/// ---------------------------------------------------------------------------

let rec length_blanks (n: nat) : Lemma (L.length (blanks n) == n) =
  if n = 0 then () else length_blanks (n - 1)

let rec nth_blanks (n: nat) (i: nat)
  : Lemma (ensures (match M1.nth (blanks n) i with Some w -> w == blank | None -> True))
          (decreases n)
  = if n = 0 then () else if i = 0 then () else nth_blanks (n - 1) (i - 1)

let rec counted_blanks (n: nat) : Lemma (counted (blanks n) == 0) =
  if n = 0 then () else counted_blanks (n - 1)

let start_fx (k: cfg) (g: heap) : fx = { fh = g; fws = blanks (nr k); fom = false; fn = 0 }

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let sinv_start (k: cfg) (g: heap) (roots: list obj_addr)
  : Lemma (requires ctx k g roots) (ensures sinv k g roots (start_fx k g) [])
  = ctx_elim k g roots;
    reveal_opaque (`%sinv) (sinv k g roots (start_fx k g) []);
    length_blanks (nr k);
    counted_blanks (nr k);
    FStar.Classical.forall_intro (nth_blanks (nr k));
    recoloured_refl g;
    let col (x: obj_addr) : Lemma (requires Seq.mem x (objs g)) (ensures ~(is_gray x g) /\ ~(is_black x g)) =
      () in
    FStar.Classical.forall_intro (FStar.Classical.move_requires col)
#pop-options

/// ---------------------------------------------------------------------------
/// One root
/// ---------------------------------------------------------------------------

let srec_recolour (k: cfg) (g h: heap) (i: nat) (w: wk) (c: obj_addr)
  : Lemma (requires srec_ok k g h i w /\ is_white c h)
          (ensures srec_ok k g (set_object_color c h Gray) i w /\ ~(L.memP c w.stack))
  = colors c h;
    let aux (y: obj_addr) : Lemma (requires L.memP y w.stack) (ensures is_gray y (set_object_color c h Gray)) =
      colors y h; Own.other_color h c y Gray in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// Greying the white c, before it is pushed.
#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let sinv_grey (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (done: list obj_addr) (c: obj_addr)
  : Lemma (requires sinv k g roots f done /\ Seq.mem c (objs g) /\ is_white c f.fh /\
                    ~(is_blue c g) /\ M1.reachable g roots c)
          (ensures (let h' = makeGray_x c f.fh in
                    recoloured g h' /\ is_gray c h' /\
                    (forall (x: obj_addr). x <> c ==>
                       is_gray x h' == is_gray x f.fh /\ is_white x h' == is_white x f.fh /\
                       is_black x h' == is_black x f.fh) /\
                    (forall (i: nat) (w: wk). FX.fwk f i == Some w ==>
                       srec_ok k g h' i w /\ ~(L.memP c w.stack))))
  = reveal_opaque (`%sinv) (sinv k g roots f done);
    makeGray_eq c f.fh;
    recoloured_blue g f.fh c;
    recoloured_makeGray g f.fh c;
    makeGray_is_gray c f.fh;
    I1.others_keep f.fh c Gray;
    let rc (i: nat) (w: wk)
      : Lemma (requires FX.fwk f i == Some w)
              (ensures srec_ok k g (makeGray_x c f.fh) i w /\ ~(L.memP c w.stack))
      = srec_recolour k g f.fh i w c
    in
    FStar.Classical.forall_intro_2 (fun i w -> FStar.Classical.move_requires (rc i) w)
#pop-options

/// What sinv says about the fx after greying c, before the push.
let grey_pre (k: cfg) (g: heap) (roots: list obj_addr) (f1: fx) (done: list obj_addr) (r c: obj_addr) : prop =
  L.length f1.fws == nr k /\ recoloured g f1.fh /\
  (forall (i: nat) (w: wk). FX.fwk f1 i == Some w ==> srec_ok k g f1.fh i w /\ ~(L.memP c w.stack)) /\
  f1.fn == counted f1.fws /\
  (forall (x: obj_addr). Seq.mem x (objs g) /\ is_gray x f1.fh /\ x <> c ==>
     L.memP x (FX.fstack f1 (own k x)) \/ f1.fom) /\
  (forall (x: obj_addr). Seq.mem x (objs g) ==> ~(is_black x f1.fh)) /\
  (forall (x: obj_addr). Seq.mem x (objs g) /\ is_gray x f1.fh ==> M1.reachable g roots x) /\
  (forall (r': obj_addr). L.memP r' (r :: done) ==> ~(is_white (resolve_object r' g) f1.fh)) /\
  Seq.mem c (objs g) /\ is_gray c f1.fh

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let grey_pre_intro (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (done: list obj_addr) (r c: obj_addr)
  : Lemma (requires sinv k g roots f done /\ Seq.mem c (objs g) /\ is_white c f.fh /\
                    ~(is_blue c g) /\ M1.reachable g roots c /\ resolve_object r g == c)
          (ensures grey_pre k g roots { f with fh = makeGray_x c f.fh } done r c)
  = sinv_grey k g roots f done c;
    reveal_opaque (`%sinv) (sinv k g roots f done);
    colors c (makeGray_x c f.fh)
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let push_full_s (k: cfg) (g: heap) (roots: list obj_addr) (f1: fx) (done: list obj_addr) (r c: obj_addr) (w: wk)
  : Lemma (requires grey_pre k g roots f1 done r c /\ FX.fwk f1 (own k c) == Some w /\
                    L.length w.stack >= k.cap_s /\ FX.push_shape k f1 c (push_fx k f1 c))
          (ensures sinv k g roots (push_fx k f1 c) (r :: done))
  = reveal_opaque (`%sinv) (sinv k g roots (push_fx k f1 c) (r :: done))
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let push_room_s (k: cfg) (g: heap) (roots: list obj_addr) (f1: fx) (done: list obj_addr) (r c: obj_addr) (w: wk)
  : Lemma (requires grey_pre k g roots f1 done r c /\ FX.fwk f1 (own k c) == Some w /\
                    L.length w.stack < k.cap_s /\ FX.push_shape k f1 c (push_fx k f1 c))
          (ensures sinv k g roots (push_fx k f1 c) (r :: done))
  = reveal_opaque (`%sinv) (sinv k g roots (push_fx k f1 c) (r :: done));
    LS.counted_set f1.fws (own k c) { w with stack = c :: w.stack };
    assert (srec_ok k g f1.fh (own k c) w);
    assert (srec_ok k g f1.fh (own k c) { w with stack = c :: w.stack })
#pop-options

/// The fx after greying c and pushing it, or setting fom.
let sinv_push (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (done: list obj_addr)
    (r c: obj_addr)
  : Lemma (requires sinv k g roots f done /\ Seq.mem c (objs g) /\ is_white c f.fh /\
                    ~(is_blue c g) /\ M1.reachable g roots c /\ resolve_object r g == c)
          (ensures sinv k g roots (push_fx k { f with fh = makeGray_x c f.fh } c) (r :: done))
  = let f1 = { f with fh = makeGray_x c f.fh } in
    grey_pre_intro k g roots f done r c;
    own_lt k c;
    FX.push_facts k f1 c;
    Own.nth_lt f1.fws (own k c);
    let Some w = M1.nth f1.fws (own k c) in
    if L.length w.stack >= k.cap_s then push_full_s k g roots f1 done r c w
    else push_room_s k g roots f1 done r c w

let sinv_skip (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (done: list obj_addr) (r: obj_addr)
  : Lemma (requires sinv k g roots f done /\ ~(is_white (resolve_object r g) f.fh))
          (ensures sinv k g roots f (r :: done))
  = reveal_opaque (`%sinv) (sinv k g roots f done);
    reveal_opaque (`%sinv) (sinv k g roots f (r :: done))

/// The object a root names.
let root_facts (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (done: list obj_addr) (r: obj_addr)
  : Lemma (requires ctx k g roots /\ sinv k g roots f done /\ L.memP r roots)
          (ensures (let c = resolve_object r g in
                    resolve_x r f.fh == c /\ Seq.mem c (objs g) /\ M1.reachable g roots c /\
                    (is_white c f.fh ==> ~(is_blue c g))))
  = reveal_opaque (`%sinv) (sinv k g roots f done);
    ctx_elim k g roots;
    let c = resolve_object r g in
    R.root_objs_mem g roots c;
    R.root_obj_facts g roots c;
    R.root_reachable g roots c;
    colors c f.fh;
    recoloured_blue g f.fh c

let darken_step (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (done: list obj_addr) (r: obj_addr)
  : Lemma (requires ctx k g roots /\ sinv k g roots f done /\ L.memP r roots)
          (ensures sinv k g roots (darken k f r) (r :: done))
  = root_facts k g roots f done r;
    let c = resolve_object r g in
    if is_white_x c f.fh then sinv_push k g roots f done r c
    else sinv_skip k g roots f done r

/// sinv reads the roots done only by membership.
let sinv_same (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (d1 d2: list obj_addr)
  : Lemma (requires sinv k g roots f d1 /\ (forall (r: obj_addr). L.memP r d2 ==> L.memP r d1))
          (ensures sinv k g roots f d2)
  = reveal_opaque (`%sinv) (sinv k g roots f d1);
    reveal_opaque (`%sinv) (sinv k g roots f d2)

let rec setup_step (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (done rest: list obj_addr)
  : Lemma (requires ctx k g roots /\ sinv k g roots f done /\
                    (forall (r: obj_addr). L.memP r rest ==> L.memP r roots))
          (ensures sinv k g roots (setup k f rest) (rest @ done))
          (decreases rest)
  = match rest with
    | [] -> ()
    | r :: tl ->
      darken_step k g roots f done r;
      setup_step k g roots (darken k f r) (r :: done) tl;
      FStar.Classical.forall_intro (L.append_memP tl (r :: done));
      FStar.Classical.forall_intro (L.append_memP rest done);
      sinv_same k g roots (setup k (darken k f r) tl) (tl @ (r :: done)) (rest @ done)

/// ---------------------------------------------------------------------------
/// The initial state
/// ---------------------------------------------------------------------------

let st0 (f: fx) : state = { heap = f.fh; wks = f.fws; count = f.fn; ovf_main = f.fom; finished = false }

let srec_at (k: cfg) (g: heap) (f: fx) (i: nat) : prop =
  match FX.fwk f i with Some w -> srec_ok k g f.fh i w | None -> True

/// The record facts of sinv, one index at a time.
let sinv_recs (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (d: list obj_addr)
  : Lemma (requires sinv k g roots f d)
          (ensures L.length f.fws == nr k /\ f.fn == counted f.fws /\ recoloured g f.fh /\
                   (forall (i: nat). srec_at k g f i))
  = reveal_opaque (`%sinv) (sinv k g roots f d);
    let aux (i: nat) : Lemma (srec_at k g f i) =
      match FX.fwk f i with Some w -> () | None -> () in
    FStar.Classical.forall_intro aux

let init_own (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (d: list obj_addr)
  : Lemma (requires sinv k g roots f d) (ensures own_ok k g (st0 f))
  = sinv_recs k g roots f d;
    reveal_opaque (`%own_ok) (own_ok k g (st0 f));
    let aux (i: nat) (w: wk) : Lemma (requires wk_of (st0 f) i == Some w) (ensures wk_ok k g f.fh i w) =
      assert (srec_at k g f i) in
    introduce forall (i: nat) (w: wk). wk_of (st0 f) i == Some w ==> wk_ok k g f.fh i w
    with introduce _ ==> _ with aux i w

let init_count (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (d: list obj_addr)
  : Lemma (requires sinv k g roots f d) (ensures count_ok (st0 f))
  = sinv_recs k g roots f d;
    reveal_opaque (`%count_ok) (count_ok (st0 f));
    let aux (i: nat) (w: wk) : Lemma (requires wk_of (st0 f) i == Some w) (ensures ~(Stopped? w.pc)) =
      assert (srec_at k g f i) in
    introduce forall (i: nat) (w: wk). wk_of (st0 f) i == Some w /\ Stopped? w.pc ==> (st0 f).count == 0
    with introduce _ ==> _ with aux i w

let init_flag (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (d: list obj_addr)
  : Lemma (requires sinv k g roots f d) (ensures flagged (st0 f) == f.fom)
  = sinv_recs k g roots f d;
    let aux (i: nat) (w: wk) : Lemma (requires M1.nth f.fws i == Some w) (ensures w.ovf == false) =
      assert (srec_at k g f i) in
    introduce forall (i: nat) (w: wk). M1.nth f.fws i == Some w ==> w.ovf == false
    with introduce _ ==> _ with aux i w;
    FStar.Classical.move_requires LS.any_ovf_elim f.fws

let init_grey (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (d: list obj_addr)
  : Lemma (requires sinv k g roots f d) (ensures grey_ok k g (st0 f))
  = init_flag k g roots f d;
    reveal_opaque (`%sinv) (sinv k g roots f d);
    reveal_opaque (`%grey_ok) (grey_ok k g (st0 f));
    assert (forall (i: nat). stack_of (st0 f) i == FX.fstack f i)

let init_sound (k: cfg) (g: heap) (roots: list obj_addr) (f: fx) (d: list obj_addr)
  : Lemma (requires sinv k g roots f d) (ensures sound g roots (st0 f) /\ fin_ok (st0 f))
  = sinv_recs k g roots f d;
    reveal_opaque (`%sinv) (sinv k g roots f d);
    reveal_opaque (`%sound) (sound g roots (st0 f));
    reveal_opaque (`%fin_ok) (fin_ok (st0 f));
    let aux (i: nat) (v: obj_addr) : Lemma (~(holds (st0 f) i v)) =
      assert (srec_at k g f i) in
    FStar.Classical.forall_intro_2 aux

let init_core (k: cfg) (g: heap) (roots: list obj_addr) (f: fx)
  : Lemma (requires sinv k g roots f (roots @ []))
          (ensures (let s = st0 f in
                    own_ok k g s /\ count_ok s /\ grey_ok k g s /\ sound g roots s /\ fin_ok s))
  = init_own k g roots f (roots @ []);
    init_count k g roots f (roots @ []);
    init_grey k g roots f (roots @ []);
    init_sound k g roots f (roots @ [])

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let init_rest (k: cfg) (g: heap) (roots: list obj_addr) (f: fx)
  : Lemma (requires sinv k g roots f (roots @ []))
          (ensures (let s = { heap = f.fh; wks = f.fws; count = f.fn; ovf_main = f.fom; finished = false } in
                    roots_ok g roots s /\ black_ok k g s))
  = let s = { heap = f.fh; wks = f.fws; count = f.fn; ovf_main = f.fom; finished = false } in
    reveal_opaque (`%sinv) (sinv k g roots f (roots @ []));
    reveal_opaque (`%roots_ok) (roots_ok g roots s);
    reveal_opaque (`%black_ok_but) (black_ok_but k g s None);
    L.append_l_nil roots;
    let rt (c: obj_addr) : Lemma (requires L.memP c (M1.root_objs g roots)) (ensures ~(is_white c s.heap)) =
      R.root_objs_mem g roots c;
      let r = FStar.IndefiniteDescription.indefinite_description_ghost obj_addr
                (fun r -> L.memP r roots /\ c == resolve_object r g) in
      ()
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires rt)
#pop-options

let init_inv (k: cfg) (g: heap) (roots: list obj_addr)
  : Lemma (requires ctx k g roots) (ensures inv k g roots (init k g roots))
  = sinv_start k g roots;
    setup_step k g roots (start_fx k g) [] roots;
    let f = setup k (start_fx k g) roots in
    init_core k g roots f;
    init_rest k g roots f
