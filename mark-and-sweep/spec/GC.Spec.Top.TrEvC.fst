/// ---------------------------------------------------------------------------
/// GC.Spec.Top.TrEvC - the correspondence across the program's writes
/// ---------------------------------------------------------------------------
///
/// Design doc §16.15.  A write changes one field of one visible block (major,
/// through the barrier, or young); the reference write changes the same
/// field of the block's object, to the written value's reference value.
/// The block is not a closure, so pointers into closures resolve as before.

module GC.Spec.Top.TrEvC

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Views
open GC.Spec.Top.Words
open GC.Spec.Top.RInv
open GC.Spec.Top.StepBase
open GC.Spec.Top.Point
open GC.Spec.Top.Transp
open GC.Spec.Top.TrRef
open GC.Spec.Top.TrVis
open GC.Spec.Top.TrGen
open GC.Spec.Top.TrIP
open GC.Spec.Top.TrEvA
open GC.Spec.Top.TrEvB
module L = FStar.List.Tot
module C = FStar.Classical
module ID = FStar.IndefiniteDescription

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

let cs_of (#c: comps) (x: config c) (e: event) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x e rn r) (ensures concl_point x /\ concl_step x e (step c x e))
  = ctx x e rn r

/// What a write leaves to the reference side: block `p`'s field `i` is
/// now `v`, every other word of a visible block is unchanged.
let write_w (rn: renaming) (w w': world) (r: rstore) (p: ptr) (i: nat) (v: value) : prop =
  ip_ctx rn w w' r /\ r_res w /\ w'.roots == w.roots /\
  visible w p /\ i < wz_of (ph w p) (pa p) /\ tag_of (ph w p) (pa p) <> closure_tag /\
  (scannable (tag_of (ph w p) (pa p)) ==> value_ok w v) /\
  fld w' p i == v /\
  (forall (q: ptr) (j: nat). visible w q /\ j < wz_of (ph w q) (pa q) /\ ~(q == p /\ j == i) ==> fld w' q j == fld w q j) /\
  (* the nursery's pointers into the major heap: old ones, or the written value *)
  (forall (y j: nat) (q: ptr). ptr_field w'.yng y j /\ target w' (field w'.yng y j) == Some q /\ Major? q ==>
     img w pid None q)

let write_w_intro (rn: renaming) (w w': world) (r: rstore) (p: ptr) (i: nat) (v: value)
  : Lemma (requires ip_ctx rn w w' r /\ r_res w /\ w'.roots == w.roots /\
                    visible w p /\ i < wz_of (ph w p) (pa p) /\ tag_of (ph w p) (pa p) <> closure_tag /\
                    (scannable (tag_of (ph w p) (pa p)) ==> value_ok w v) /\
                    fld w' p i == v /\
                    (forall (q: ptr) (j: nat). visible w q /\ j < wz_of (ph w q) (pa q) /\ ~(q == p /\ j == i) ==>
                       fld w' q j == fld w q j) /\
                    (forall (y j: nat) (q: ptr). ptr_field w'.yng y j /\ target w' (field w'.yng y j) == Some q /\ Major? q ==>
                       img w pid None q))
          (ensures write_w rn w w' r p i v)
  = ()

/// ---------------------------------------------------------------------------
/// The reference side
/// ---------------------------------------------------------------------------

let write_obj (rn: renaming) (w w': world) (r: rstore) (p: ptr) (i: nat) (v: value) (k k': nat)
  : Lemma (requires write_w rn w w' r p i v /\ rn k == Some p /\ Some? (r.objs k) /\ Some? (rn k') /\
                    rwf r /\ vcorr (rn_step rn pid r.next None) w' (scannable (robj_of r k).rtag) v
                                  (trv rn w r (scannable (robj_of r k).rtag) v))
          (ensures (let r' = rstep r (RWrite k i (trv rn w r (scannable (robj_of r k).rtag) v)) in
                    Some? (r'.objs k') /\ ocorr (rn_step rn pid r.next None) w' (Some?.v (rn k')) (Some?.v (r'.objs k'))))
  = let rv = trv rn w r (scannable (robj_of r k).rtag) v in
    let r' = rstep r (RWrite k i rv) in
    let p' = Some?.v (rn k') in
    assert (visible w p');
    name_ocorr rn w r k' p';
    if k' = k then begin
      let ro = Some?.v (r.objs k) in
      let ro' = Some?.v (r'.objs k) in
      assert (ro'.rtag == ro.rtag /\ ro'.rsz == ro.rsz);
      assert (forall (j: nat). j <> i ==> ro'.rf j == ro.rf j);
      assert (ro'.rf i == rv);
      ocorr_keep rn r.next None w w' r k p ro'
    end else begin
      assert (p' =!= p);
      assert (r'.objs k' == r.objs k');
      ocorr_keep rn r.next None w w' r k' p' (robj_of r k')
    end

/// **The reference side of a write.**
let write_ref (rn: renaming) (w w': world) (r: rstore) (p: ptr) (i: nat) (v: value)
  : Lemma (requires scorr_w rn w r /\ clean rn w r /\ rwf r /\ write_w rn w w' r p i v)
          (ensures (let k = name_of rn r p in
                    let rv = trv rn w r (scannable (robj_of r k).rtag) v in
                    exists (rn': renaming). rok r (RWrite k i rv) /\ ev_corr rn w r (EWrite p i v) (RWrite k i rv) /\
                      scorr_w rn' w' (rstep r (RWrite k i rv)) /\ clean rn' w' (rstep r (RWrite k i rv))))
  = name_vis rn w r p;
    let k = name_of rn r p in
    let ro = Some?.v (r.objs k) in
    let scan = scannable ro.rtag in
    let rv = trv rn w r scan v in
    let re = RWrite k i rv in
    let r' = rstep r re in
    tr_move rn r.next None w w' r scan v;
    assert (rok r re /\ ev_corr rn w r (EWrite p i v) re);
    rwf_step r re;
    roots_same rn r.next None w w' r;
    assert (r'.rroots == r.rroots);
    let f (k': nat)
      : Lemma (Some? (rn k') ==> Some? (r'.objs k') /\
                 ocorr (rn_step rn pid r.next None) w' (pid (Some?.v (rn k'))) (Some?.v (r'.objs k')))
      = if Some? (rn k') then write_obj rn w w' r p i v k k' in
    C.forall_intro f;
    finish rn r.next None w w' r r'

/// ---------------------------------------------------------------------------
/// Major writes
/// ---------------------------------------------------------------------------

let mwrite_cw (#c: comps) (x: config c) (o i: nat) (v: value)
  : Lemma (ensures (step c x (EWrite (Major o) i v)).w.croots == x.w.croots /\
                   (step c x (EWrite (Major o) i v)).w.cyng == x.w.cyng)
  = ()

/// The fields after a major write (small context: no `sim_pre`).
let mwrite_fld_core (#c: comps) (x: config c) (o i: nat) (v: value) (q: ptr) (j: nat)
  : Lemma (requires concl_point x /\ concl_step x (EWrite (Major o) i v) (step c x (EWrite (Major o) i v)) /\
                    agree (vw x).yng (vw (step c x (EWrite (Major o) i v))).yng /\
                    tag_of (mj x) o <> closure_tag /\
                    visible (vw x) q /\ j < wz_of (ph (vw x) q) (pa q))
          (ensures fld (vw (step c x (EWrite (Major o) i v))) q j ==
                   (if Major? q && pa q = o && j = i then v else fld (vw x) q j))
  = let e = EWrite (Major o) i v in
    let w = vw x in
    let w' = vw (step c x e) in
    match q with
    | Major o' ->
      maj_vis x e o';
      assert (field (mj (step c x e)) o' j == new_field x e o' j)
    | Young y ->
      yvis_block w y;
      yng_agree_keep w w' y;
      assert (j < wz_of w.yng y);
      assert (fld w' q j == field w'.yng y j /\ fld w q j == field w.yng y j);
      assert (field w'.yng y j == field w.yng y j)

let mwrite_fld (#c: comps) (x: config c) (o i: nat) (v: value) (rn: renaming) (r: rstore) (q: ptr) (j: nat)
  : Lemma (requires sim_pre x (EWrite (Major o) i v) rn r /\
                    agree (vw x).yng (vw (step c x (EWrite (Major o) i v))).yng /\
                    tag_of (mj x) o <> closure_tag /\
                    visible (vw x) q /\ j < wz_of (ph (vw x) q) (pa q))
          (ensures fld (vw (step c x (EWrite (Major o) i v))) q j ==
                   (if Major? q && pa q = o && j = i then v else fld (vw x) q j))
  = cs_of x (EWrite (Major o) i v) rn r;
    mwrite_fld_core x o i v q j

/// Every other word of a visible block is unchanged (sealed, so it travels
/// through the large contexts below as one fact).
[@@"opaque_to_smt"]
let others_kept (w w': world) (p: ptr) (i: nat) : prop =
  forall (q: ptr) (j: nat). visible w q /\ j < wz_of (ph w q) (pa q) /\ ~(q == p /\ j == i) ==> fld w' q j == fld w q j

let mwrite_flds (#c: comps) (x: config c) (o i: nat) (v: value)
  : Lemma (requires concl_point x /\ concl_step x (EWrite (Major o) i v) (step c x (EWrite (Major o) i v)) /\
                    agree (vw x).yng (vw (step c x (EWrite (Major o) i v))).yng /\
                    tag_of (mj x) o <> closure_tag)
          (ensures others_kept (vw x) (vw (step c x (EWrite (Major o) i v))) (Major o) i)
  = let f (q: ptr) (j: nat)
      : Lemma (requires visible (vw x) q /\ j < wz_of (ph (vw x) q) (pa q) /\ ~(q == Major o /\ j == i))
              (ensures fld (vw (step c x (EWrite (Major o) i v))) q j == fld (vw x) q j)
      = mwrite_fld_core x o i v q j in
    C.forall_intro_2 (fun q j -> C.move_requires (f q) j);
    reveal_opaque (`%others_kept) others_kept

let write_w_kept (rn: renaming) (w w': world) (r: rstore) (p: ptr) (i: nat) (v: value)
  : Lemma (requires ip_ctx rn w w' r /\ r_res w /\ w'.roots == w.roots /\
                    visible w p /\ i < wz_of (ph w p) (pa p) /\ tag_of (ph w p) (pa p) <> closure_tag /\
                    (scannable (tag_of (ph w p) (pa p)) ==> value_ok w v) /\
                    fld w' p i == v /\ others_kept w w' p i /\
                    (forall (y j: nat) (q: ptr). ptr_field w'.yng y j /\ target w' (field w'.yng y j) == Some q /\ Major? q ==>
                       img w pid None q))
          (ensures write_w rn w w' r p i v)
  = reveal_opaque (`%others_kept) others_kept;
    write_w_intro rn w w' r p i v

let mwrite_world (#c: comps) (x: config c) (o i: nat) (v: value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EWrite (Major o) i v) rn r)
          (ensures write_w rn (vw x) (vw (step c x (EWrite (Major o) i v))) r (Major o) i v)
  = let e = EWrite (Major o) i v in
    let x' = step c x e in
    ctx x e rn r;
    mwrite_cw x o i v;
    yng_same x x';
    assert (mutator_ok_w c (vw x) e);
    ip_of x e rn r;
    let w = vw x in
    let w' = vw x' in
    maj_vis x e o;
    mwrite_fld_core x o i v (Major o) i;
    mwrite_flds x o i v;
    yrefs_same rn None w w' r;
    assert (ip_ctx rn w w' r /\ r_res w);
    assert (w'.roots == w.roots);
    assert (visible w (Major o) /\ i < wz_of w.maj o /\ tag_of w.maj o <> closure_tag);
    assert (scannable (tag_of w.maj o) ==> value_ok w v);
    assert (fld w' (Major o) i == v);
    assert (ph w (Major o) == w.maj /\ pa (Major o) == o);
    assert (forall (y j: nat) (q: ptr). ptr_field w'.yng y j /\ target w' (field w'.yng y j) == Some q /\ Major? q ==>
              img w pid None q);
    write_w_kept rn w w' r (Major o) i v

/// **A major write.**
let sim_mwrite (#c: comps) (x: config c) (o i: nat) (v: value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EWrite (Major o) i v) rn r) (ensures sim_post x (EWrite (Major o) i v) rn r)
  = let e = EWrite (Major o) i v in
    let x' = step c x e in
    let w = vw x in
    mwrite_world x o i v rn r;
    scorr_eq rn x r;
    write_ref rn w (vw x') r (Major o) i v;
    let k = name_of rn r (Major o) in
    let re = RWrite k i (trv rn w r (scannable (robj_of r k).rtag) v) in
    eliminate exists (rn': renaming). rok r re /\ ev_corr rn w r e re /\
                                       scorr_w rn' (vw x') (rstep r re) /\ clean rn' (vw x') (rstep r re)
    with post_mut x e rn r re rn'

/// ---------------------------------------------------------------------------
/// Young writes
/// ---------------------------------------------------------------------------

/// The nursery after a young write.
let ywrite_yng (#c: comps) (x: config c) (o i: nat) (v: value)
  : Lemma (requires faithful c.r /\ rinv x /\ hyps_at c x (EWrite (Young o) i v) /\ mutator_ok x (EWrite (Young o) i v) /\
                    rinv (step c x (EWrite (Young o) i v)))
          (ensures agree (set_field (vw x).yng o i v) (vw (step c x (EWrite (Young o) i v))).yng)
  = let e = EWrite (Young o) i v in
    let x' = step c x e in
    vw_views x;
    vw_views x';
    assert (mutator_ok_w c (vw x) e);
    assert (c.r.yrepr (set_field (vw x).yng o i v) (c.r.ywrite x.w.cyng o i v));
    yrepr_agree c.r (set_field (vw x).yng o i v) (vw x').yng x'.w.cyng

let yw_field (w w': world) (o i: nat) (v: value) (y j: nat)
  : Lemma (requires agree (set_field w.yng o i v) w'.yng /\ young_ok w.yng /\ is_block w.yng y /\
                    is_block w.yng o /\ i < wz_of w.yng o /\ j < wz_of w.yng y)
          (ensures field w'.yng y j == (if y = o && j = i then v else field w.yng y j))
  = let m = set_field w.yng o i v in
    ag_hd m w'.yng y;
    ag_field m w'.yng y j;
    assert (covers w.yng y (y + 1 + j) /\ covers w.yng o (o + 1 + i));
    if y + 1 + j = o + 1 + i then assert (y == o)

let yw_keep (w w': world) (o i: nat) (v: value) (y: nat)
  : Lemma (requires agree (set_field w.yng o i v) w'.yng /\ young_ok w.yng /\ is_block w.yng y /\ is_block w.yng o /\
                    i < wz_of w.yng o /\ tag_of w.yng o <> closure_tag)
          (ensures shape_keep w.yng w'.yng y y /\
                   (forall (j: nat). j < wz_of w.yng y ==> field w'.yng y j == (if y = o && j = i then v else field w.yng y j)))
  = let m = set_field w.yng o i v in
    ag_hd m w'.yng y;
    C.forall_intro (C.move_requires (yw_field w w' o i v y))

let ywrite_fld (#c: comps) (x: config c) (o i: nat) (v: value) (rn: renaming) (r: rstore) (q: ptr) (j: nat)
  : Lemma (requires sim_pre x (EWrite (Young o) i v) rn r /\
                    agree (set_field (vw x).yng o i v) (vw (step c x (EWrite (Young o) i v))).yng /\
                    is_block (vw x).yng o /\ i < wz_of (vw x).yng o /\ tag_of (vw x).yng o <> closure_tag /\
                    young_ok (vw x).yng /\ visible (vw x) q)
          (ensures shape_keep (ph (vw x) q) (ph (vw (step c x (EWrite (Young o) i v))) q) (pa q) (pa q) /\
                   (j < wz_of (ph (vw x) q) (pa q) ==>
                      fld (vw (step c x (EWrite (Young o) i v))) q j == (if Young? q && pa q = o && j = i then v else fld (vw x) q j)))
  = let e = EWrite (Young o) i v in
    cs_of x e rn r;
    let w = vw x in
    let w' = vw (step c x e) in
    match q with
    | Major o' ->
      maj_vis x e o';
      assert (j < wz_of w.maj o' ==> field (mj (step c x e)) o' j == new_field x e o' j)
    | Young y -> yvis_block w y; yw_keep w w' o i v y

/// The nursery's major pointers after a young write.
let ywrite_yref (rn: renaming) (w w': world) (r: rstore) (o i: nat) (v: value) (y j: nat) (q: ptr)
  : Lemma (requires ip_ctx rn w w' r /\ r_res w /\ agree (set_field w.yng o i v) w'.yng /\
                    is_block w.yng o /\ i < wz_of w.yng o /\ tag_of w.yng o <> closure_tag /\ young_ok w.yng /\
                    (scannable (tag_of w.yng o) ==> value_ok w v) /\
                    ptr_field w'.yng y j /\ target w' (field w'.yng y j) == Some q /\ Major? q)
          (ensures img w pid None q)
  = let m = set_field w.yng o i v in
    agree_sym m w'.yng;
    ag_ptr_field w'.yng m y j;
    assert (is_block w.yng y /\ ptr_field w.yng y j);
    yw_field w w' o i v y j;
    let u = field w'.yng y j in
    if y = o && j = i then begin
      assert (u == v /\ value_ok w v);
      maj_target rn w w' r None u q
    end else begin
      assert (u == field w.yng y j);
      res_yng w y j;
      let aux (q0: ptr) : Lemma (requires target w u == Some q0) (ensures visible w q0)
        = vis_young w y j q0 in
      C.forall_intro (C.move_requires aux);
      maj_target rn w w' r None u q
    end

let yw_agree (#c: comps) (x: config c) (o i: nat) (v: value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EWrite (Young o) i v) rn r)
          (ensures agree (set_field (vw x).yng o i v) (vw (step c x (EWrite (Young o) i v))).yng)
  = step_ok x (EWrite (Young o) i v);
    ywrite_yng x o i v

let yw_pre (#c: comps) (x: config c) (o i: nat) (v: value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EWrite (Young o) i v) rn r)
          (ensures (let w = vw x in let w' = vw (step c x (EWrite (Young o) i v)) in
                    agree (set_field w.yng o i v) w'.yng /\
                    is_block w.yng o /\ i < wz_of w.yng o /\ tag_of w.yng o <> closure_tag /\ visible w (Young o) /\
                    young_ok w.yng /\ (scannable (tag_of w.yng o) ==> value_ok w v) /\
                    w'.roots == w.roots /\ uc w'.maj /\ uc w'.yng /\ r_res w /\
                    scorr_w rn w r /\ clean rn w r /\ rwf r))
  = let e = EWrite (Young o) i v in
    let x' = step c x e in
    yw_agree x o i v rn r;
    ctx x e rn r;
    assert (x'.w.croots == x.w.croots);
    assert (mutator_ok_w c (vw x) e)

let yw_shapes (#c: comps) (x: config c) (o i: nat) (v: value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EWrite (Young o) i v) rn r)
          (ensures (let w = vw x in let w' = vw (step c x (EWrite (Young o) i v)) in
                    (forall (q: ptr). visible w q ==> shape_keep (ph w q) (ph w' q) (pa q) (pa q)) /\
                    (forall (q: ptr) (j: nat). visible w q /\ j < wz_of (ph w q) (pa q) ==>
                       fld w' q j == (if Young? q && pa q = o && j = i then v else fld w q j))))
  = yw_pre x o i v rn r;
    let w = vw x in
    let w' = vw (step c x (EWrite (Young o) i v)) in
    let f (q: ptr) : Lemma (visible w q ==> shape_keep (ph w q) (ph w' q) (pa q) (pa q))
      = if ID.strong_excluded_middle (visible w q) then ywrite_fld x o i v rn r q 0 in
    let g (q: ptr) (j: nat)
      : Lemma (visible w q /\ j < wz_of (ph w q) (pa q) ==>
                 fld w' q j == (if Young? q && pa q = o && j = i then v else fld w q j))
      = if ID.strong_excluded_middle (visible w q) then ywrite_fld x o i v rn r q j in
    C.forall_intro f;
    C.forall_intro_2 g

let ywrite_world (#c: comps) (x: config c) (o i: nat) (v: value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EWrite (Young o) i v) rn r)
          (ensures write_w rn (vw x) (vw (step c x (EWrite (Young o) i v))) r (Young o) i v)
  = let e = EWrite (Young o) i v in
    let x' = step c x e in
    yw_pre x o i v rn r;
    let w = vw x in
    let w' = vw x' in
    yw_shapes x o i v rn r;
    assert (ip_ctx rn w w' r);
    yw_keep w w' o i v o;
    assert (fld w' (Young o) i == v);
    assert (forall (q: ptr) (j: nat). visible w q /\ j < wz_of (ph w q) (pa q) /\ ~(q == Young o /\ j == i) ==>
              fld w' q j == fld w q j);
    C.forall_intro_3 (fun (y j: nat) (q: ptr) -> C.move_requires (ywrite_yref rn w w' r o i v y j) q);
    assert (w'.roots == w.roots);
    write_w_intro rn w w' r (Young o) i v

/// **A young write.**
let sim_ywrite (#c: comps) (x: config c) (o i: nat) (v: value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EWrite (Young o) i v) rn r) (ensures sim_post x (EWrite (Young o) i v) rn r)
  = let e = EWrite (Young o) i v in
    let x' = step c x e in
    let w = vw x in
    ywrite_world x o i v rn r;
    scorr_eq rn x r;
    write_ref rn w (vw x') r (Young o) i v;
    let k = name_of rn r (Young o) in
    let re = RWrite k i (trv rn w r (scannable (robj_of r k).rtag) v) in
    eliminate exists (rn': renaming). rok r re /\ ev_corr rn w r e re /\
                                       scorr_w rn' (vw x') (rstep r re) /\ clean rn' (vw x') (rstep r re)
    with post_mut x e rn r re rn'
