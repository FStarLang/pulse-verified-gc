/// ---------------------------------------------------------------------------
/// GC.Spec.Top.TrEvB - the correspondence across collector steps (other
/// than a minor collection), reads and root changes
/// ---------------------------------------------------------------------------
///
/// Design doc §16.15.  A collector step changes neither the roots nor the
/// nursery, nor the fields of a kept block: the reference store stays.  A
/// read pushes the field read, which is the reference field read.  A
/// root change pushes the reference values of the new roots (`trv`).

module GC.Spec.Top.TrEvB

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Views
open GC.Spec.Top.RInv
open GC.Spec.Top.StepBase
open GC.Spec.Top.Point
open GC.Spec.Top.Transp
open GC.Spec.Top.TrRef
open GC.Spec.Top.TrVis
open GC.Spec.Top.TrGen
open GC.Spec.Top.TrIP
open GC.Spec.Top.TrEvA
module L = FStar.List.Tot
module C = FStar.Classical
module ID = FStar.IndefiniteDescription

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Helpers
/// ---------------------------------------------------------------------------

let rec gmap (f: value -> GTot rval) (l: list value) : GTot (list rval) =
  match l with
  | [] -> []
  | h :: t -> f h :: gmap f t

let rec gmap_idx (f: value -> GTot rval) (l: list value) (i: nat)
  : Lemma (ensures L.length (gmap f l) == L.length l /\ (i < L.length l ==> L.index (gmap f l) i == f (L.index l i)))
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: t -> if i = 0 then gmap_idx f t 0 else gmap_idx f t (i - 1)

/// A value naming a visible block keeps its correspondence.
let move_val (rn: renaming) (nk: nat) (nw: option ptr) (w w': world) (r: rstore) (scan: bool) (v: value) (rv: rval)
  : Lemma (requires ip_ctx rn w w' r /\ (Some? nw ==> nk == r.next) /\ vcorr rn w scan v rv /\
                    (match rv with RPtr k _ -> (exists (q: ptr). rn k == Some q /\ visible w q) | _ -> True))
          (ensures vcorr (rn_step rn pid nk nw) w' scan v rv)
  = match rv with
    | RPtr k d ->
      vcorr_ptr rn w scan v k d;
      let q = Some?.v (rn k) in
      name_ok rn w r k q;
      vmoved_id rn w w' r v;
      vcorr_move rn pid nk nw w w' scan v v rv
    | RWord _ -> vcorr_move rn pid nk nw w w' scan v v rv

/// A program value, named.
let tr_move (rn: renaming) (nk: nat) (nw: option ptr) (w w': world) (r: rstore) (scan: bool) (v: value)
  : Lemma (requires ip_ctx rn w w' r /\ (Some? nw ==> nk == r.next) /\ (scan ==> value_ok w v))
          (ensures vcorr rn w scan v (trv rn w r scan v) /\ rval_ok r scan (trv rn w r scan v) /\
                   vcorr (rn_step rn pid nk nw) w' scan v (trv rn w r scan v) /\
                   (match trv rn w r scan v with RPtr k _ -> k < r.next | _ -> True))
  = trv_ok rn w r scan v;
    move_val rn nk nw w w' r scan v (trv rn w r scan v)

/// The step's views: the roots, and the nursery kept.
let yng_same (#c: comps) (x x': config c)
  : Lemma (requires faithful c.r /\ views x (vw x) /\ views x' (vw x') /\ x'.w.cyng == x.w.cyng)
          (ensures agree (vw x).yng (vw x').yng)
  = yrepr_agree c.r (vw x).yng (vw x').yng x.w.cyng

let post_of (#c: comps) (x': config c) (r: rstore)
  : Lemma (requires exists (rn': renaming). scorr_w rn' (vw x') r /\ clean rn' (vw x') r)
          (ensures exists (rn': renaming). scorr rn' x' r /\ clean rn' (wv x') r)
  = C.forall_intro (fun (rn': renaming) -> scorr_eq rn' x' r)

/// The post of a program event, from the reference side.
let post_mut (#c: comps) (x: config c) (e: event) (rn: renaming) (r: rstore) (re: revent) (rn': renaming)
  : Lemma (requires is_mutator_event e /\ rok r re /\ ev_corr rn (wv x) r e re /\
                    scorr_w rn' (vw (step c x e)) (rstep r re) /\ clean rn' (vw (step c x e)) (rstep r re))
          (ensures sim_post x e rn r)
  = let x' = step c x e in
    scorr_eq rn' x' (rstep r re);
    introduce exists (re2: revent) (rn2: renaming).
      rok r re2 /\ ev_corr rn (wv x) r e re2 /\ scorr rn2 x' (rstep r re2) /\ clean rn2 (wv x') (rstep r re2)
    with re rn' and ()

/// The name of a visible block.
let name_vis (rn: renaming) (w: world) (r: rstore) (q: ptr)
  : Lemma (requires scorr_w rn w r /\ visible w q)
          (ensures rn (name_of rn r q) == Some q /\ Some? (r.objs (name_of rn r q)) /\
                   ocorr rn w q (Some?.v (r.objs (name_of rn r q))))
  = assert (exists (k: nat). named rn r q k);
    name_ocorr rn w r (name_of rn r q) q

/// ---------------------------------------------------------------------------
/// Collector steps
/// ---------------------------------------------------------------------------

let coll_cw (#c: comps) (x: config c) (e: event)
  : Lemma (requires ~(is_mutator_event e) /\ ~(EMinor? e))
          (ensures (step c x e).w.croots == x.w.croots /\ (step c x e).w.cyng == x.w.cyng)
  = match e with
    | ESweep -> (match x.ph with Sweeping _ -> () | _ -> ())
    | _ -> ()

/// **A collector step (not a minor collection).**
let sim_coll (#c: comps) (x: config c) (e: event) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x e rn r /\ ~(is_mutator_event e) /\ ~(EMinor? e))
          (ensures sim_post x e rn r)
  = let x' = step c x e in
    ctx x e rn r;
    coll_cw x e;
    yng_same x x';
    ip_of x e rn r;
    let w = vw x in
    let w' = vw x' in
    roots_same rn r.next None w w' r;
    yrefs_same rn None w w' r;
    C.forall_intro_2 (fun (p: ptr) (j: nat) -> C.move_requires (flds_same x e rn r p) j);
    objs_same rn r.next None w w' r r;
    finish rn r.next None w w' r r;
    post_of x' r

/// ---------------------------------------------------------------------------
/// Reads
/// ---------------------------------------------------------------------------

let read_cw (#c: comps) (x: config c) (p: ptr) (i: nat)
  : Lemma (ensures (step c x (ERead p i)).w.cyng == x.w.cyng)
  = match p with Major _ -> () | Young _ -> ()

/// What a step that keeps the nursery and every visible block's words
/// leaves to the reference side.
let same_w (rn: renaming) (w w': world) (r: rstore) : prop =
  ip_ctx rn w w' r /\ agree w.yng w'.yng /\ r_res w /\
  (forall (p: ptr) (j: nat). visible w p /\ j < wz_of (ph w p) (pa p) ==> fld w' p j == fld w p j)

let read_facts (#c: comps) (x: config c) (p: ptr) (i: nat) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (ERead p i) rn r)
          (ensures (let w = vw x in let w' = vw (step c x (ERead p i)) in
                    visible w p /\ pfield w p i /\ w'.roots == fld w p i :: w.roots))
  = let e = ERead p i in
    let x' = step c x e in
    ctx x e rn r;
    assert (mutator_ok_w c (vw x) e);
    assert (x'.w.croots == (match p with Major o -> field (mj x) o i | Young o -> field (wv x).yng o i) :: x.w.croots);
    match p with Major o -> () | Young o -> ()

let read_world (#c: comps) (x: config c) (p: ptr) (i: nat) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (ERead p i) rn r)
          (ensures (let w = vw x in let w' = vw (step c x (ERead p i)) in
                    same_w rn w w' r /\ visible w p /\ pfield w p i /\ w'.roots == fld w p i :: w.roots))
  = let e = ERead p i in
    let x' = step c x e in
    ctx x e rn r;
    read_cw x p i;
    yng_same x x';
    ip_of x e rn r;
    C.forall_intro_2 (fun (q: ptr) (j: nat) -> C.move_requires (flds_same x e rn r q) j);
    read_facts x p i rn r

/// The reference side of a read.
let read_ref (rn: renaming) (w w': world) (r: rstore) (p: ptr) (i: nat)
  : Lemma (requires same_w rn w w' r /\ visible w p /\ pfield w p i /\ w'.roots == fld w p i :: w.roots)
          (ensures exists (k: nat) (rn': renaming).
                     rok r (RRead k i) /\ ev_corr rn w r (ERead p i) (RRead k i) /\
                     scorr_w rn' w' (rstep r (RRead k i)) /\ clean rn' w' (rstep r (RRead k i)))
  = name_vis rn w r p;
    let k = name_of rn r p in
    let ro = Some?.v (r.objs k) in
    let re = RRead k i in
    let r' = rstep r re in
    assert (r'.objs == r.objs /\ r'.rroots == ro.rf i :: r.rroots);
    assert (rok r re /\ ev_corr rn w r (ERead p i) re);
    rwf_step r re;
    field_keep rn r.next None w w' r k p i;
    roots_push rn r.next None w w' r r' (fld w p i) (ro.rf i);
    yrefs_same rn None w w' r;
    objs_same rn r.next None w w' r r';
    finish rn r.next None w w' r r'

/// **A read.**
let sim_read (#c: comps) (x: config c) (p: ptr) (i: nat) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (ERead p i) rn r) (ensures sim_post x (ERead p i) rn r)
  = let x' = step c x (ERead p i) in
    read_world x p i rn r;
    read_ref rn (vw x) (vw x') r p i;
    eliminate exists (k: nat) (rn': renaming).
      rok r (RRead k i) /\ ev_corr rn (vw x) r (ERead p i) (RRead k i) /\
      scorr_w rn' (vw x') (rstep r (RRead k i)) /\ clean rn' (vw x') (rstep r (RRead k i))
    with post_mut x (ERead p i) rn r (RRead k i) rn'

/// ---------------------------------------------------------------------------
/// Root changes
/// ---------------------------------------------------------------------------

let roots_world (#c: comps) (x: config c) (rs: list value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (ERoots rs) rn r)
          (ensures (let w = vw x in let w' = vw (step c x (ERoots rs)) in
                    same_w rn w w' r /\ w'.roots == rs /\ (forall (v: value). L.memP v rs ==> value_ok w v)))
  = let e = ERoots rs in
    let x' = step c x e in
    ctx x e rn r;
    yng_same x x';
    ip_of x e rn r;
    C.forall_intro_2 (fun (q: ptr) (j: nat) -> C.move_requires (flds_same x e rn r q) j);
    assert (mutator_ok_w c (vw x) e)

/// The new roots, named, one by one.
let roots_pt (rn: renaming) (w w': world) (r: rstore) (rs: list value) (j: nat)
  : Lemma (requires same_w rn w w' r /\ (forall (v: value). L.memP v rs ==> value_ok w v) /\ j < L.length rs)
          (ensures j < L.length (gmap (trv rn w r true) rs) /\
                   L.index (gmap (trv rn w r true) rs) j == trv rn w r true (L.index rs j) /\
                   vcorr rn w true (L.index rs j) (trv rn w r true (L.index rs j)) /\
                   rval_ok r true (trv rn w r true (L.index rs j)) /\
                   vcorr (rn_step rn pid r.next None) w' true (L.index rs j) (trv rn w r true (L.index rs j)))
  = gmap_idx (trv rn w r true) rs j;
    idx_memP rs j;
    tr_move rn r.next None w w' r true (L.index rs j)

/// The reference side of a change of the roots.
let roots_ref (rn: renaming) (w w': world) (r: rstore) (rs: list value)
  : Lemma (requires same_w rn w w' r /\ w'.roots == rs /\ (forall (v: value). L.memP v rs ==> value_ok w v))
          (ensures (let re = RRoots (gmap (trv rn w r true) rs) in
                    exists (rn': renaming). rok r re /\ ev_corr rn w r (ERoots rs) re /\
                      scorr_w rn' w' (rstep r re) /\ clean rn' w' (rstep r re)))
  = let rvs = gmap (trv rn w r true) rs in
    let re = RRoots rvs in
    let r' = rstep r re in
    rwf_step r re;
    gmap_idx (trv rn w r true) rs 0;
    assert (L.length rvs == L.length rs);
    C.forall_intro (C.move_requires (roots_pt rn w w' r rs));
    let h (v: rval) : Lemma (requires L.memP v rvs) (ensures rval_ok r true v)
      = memP_idx v rvs in
    C.forall_intro (C.move_requires h);
    assert (rok r re);
    assert (vcorr_list rn w true rs rvs);
    assert (r'.rroots == rvs /\ r'.objs == r.objs);
    assert (roots_corr (rn_step rn pid r.next None) w' r');
    yrefs_same rn None w w' r;
    objs_same rn r.next None w w' r r';
    finish rn r.next None w w' r r'

/// **A change of the roots.**
let sim_roots (#c: comps) (x: config c) (rs: list value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (ERoots rs) rn r) (ensures sim_post x (ERoots rs) rn r)
  = let x' = step c x (ERoots rs) in
    roots_world x rs rn r;
    roots_ref rn (vw x) (vw x') r rs;
    let re = RRoots (gmap (trv rn (vw x) r true) rs) in
    eliminate exists (rn': renaming). rok r re /\ ev_corr rn (vw x) r (ERoots rs) re /\
                                       scorr_w rn' (vw x') (rstep r re) /\ clean rn' (vw x') (rstep r re)
    with post_mut x (ERoots rs) rn r re rn'
