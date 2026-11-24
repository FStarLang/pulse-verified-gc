/// ---------------------------------------------------------------------------
/// GC.Spec.Top.TrEvD - the correspondence across allocations
/// ---------------------------------------------------------------------------
///
/// Design doc §16.15.  An allocation adds one block, filled with the
/// program's values, on words no visible block uses, and pushes it as a
/// root; the reference allocation adds the next name, filled with the
/// values' reference values (`alloc_ref`).  For a major allocation the
/// block was not in use ((2)); for a young one it was free in the nursery
/// (`yalloc_ok`), and the nursery's other blocks keep their fields.

module GC.Spec.Top.TrEvD

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

/// The `i`th value (a word past the end).
let vidx (vs: list value) (i: nat) : value = if i < L.length vs then L.index vs i else VInt 0

/// What an allocation of block `np` leaves to the reference side.
let alloc_w (rn: renaming) (w w': world) (r: rstore) (np: ptr) (sz: size_t) (tag: tag_t) (vs: list value) : prop =
  ip_ctx rn w w' r /\
  w'.roots == VPtr np :: w.roots /\
  is_block (ph w' np) (pa np) /\ wz_of (ph w' np) (pa np) == sz /\ tag_of (ph w' np) (pa np) == tag /\
  (forall (i: nat). i < sz ==> fld w' np i == vidx vs i) /\
  (forall (q: ptr). visible w q ==> q =!= np) /\
  tag <> infix_tag /\ L.length vs == sz /\
  (scannable tag ==> (forall (i: nat). i < sz ==> value_ok w (vidx vs i))) /\
  (forall (p: ptr) (j: nat). visible w p /\ j < wz_of (ph w p) (pa p) ==> fld w' p j == fld w p j) /\
  (forall (y i: nat) (q: ptr). ptr_field w'.yng y i /\ target w' (field w'.yng y i) == Some q /\ Major? q ==>
     img w pid (Some np) q)

/// The new object's fields.
let new_field (rn: renaming) (w w': world) (r: rstore) (np: ptr) (sz: size_t) (tag: tag_t) (vs: list value) (i: nat)
  : Lemma (requires alloc_w rn w w' r np sz tag vs /\ i < sz)
          (ensures rlist (gmap (trv rn w r (scannable tag)) vs) i == trv rn w r (scannable tag) (vidx vs i) /\
                   vcorr rn w (scannable tag) (vidx vs i) (rlist (gmap (trv rn w r (scannable tag)) vs) i) /\
                   rval_ok r (scannable tag) (rlist (gmap (trv rn w r (scannable tag)) vs) i) /\
                   vcorr (rn_step rn pid r.next (Some np)) w' (scannable tag) (fld w' np i)
                         (rlist (gmap (trv rn w r (scannable tag)) vs) i))
  = gmap_idx (trv rn w r (scannable tag)) vs i;
    tr_move rn r.next (Some np) w w' r (scannable tag) (vidx vs i)

let new_root (rn: renaming) (w': world) (r: rstore) (np: ptr)
  : Lemma (requires is_block (ph w' np) (pa np))
          (ensures vcorr (rn_step rn pid r.next (Some np)) w' true (VPtr np) (RPtr r.next 0))
  = match np with Major _ -> () | Young _ -> ()

/// **The reference side of an allocation.**
let alloc_ref (rn: renaming) (w w': world) (r: rstore) (np: ptr) (young: bool) (sz: size_t) (tag: tag_t) (vs: list value)
  : Lemma (requires alloc_w rn w w' r np sz tag vs)
          (ensures (let rvs = gmap (trv rn w r (scannable tag)) vs in
                    let re = RAlloc young tag rvs in
                    rok r re /\ L.length rvs == sz /\ vcorr_list rn w (scannable tag) vs rvs /\
                    (exists (rn': renaming). scorr_w rn' w' (rstep r re) /\ clean rn' w' (rstep r re))))
  = let scan = scannable tag in
    let rvs = gmap (trv rn w r scan) vs in
    let re = RAlloc young tag rvs in
    let r' = rstep r re in
    let nk = r.next in
    let nw = Some np in
    gmap_idx (trv rn w r scan) vs 0;
    C.forall_intro (C.move_requires (new_field rn w w' r np sz tag vs));
    assert (rok r re /\ vcorr_list rn w scan vs rvs);
    rwf_step r re;
    let ro = Some?.v (r'.objs nk) in
    assert (ro.rtag == tag /\ ro.rsz == sz /\ (forall (i: nat). ro.rf i == rlist rvs i));
    assert (ocorr (rn_step rn pid nk nw) w' np ro);
    new_root rn w' r np;
    roots_push rn nk nw w w' r r' (VPtr np) (RPtr nk 0);
    let old (k: nat) : Lemma (Some? (rn k) ==> r'.objs k == r.objs k)
      = match rn k with Some p -> assert (k < r.next) | None -> () in
    C.forall_intro old;
    objs_same rn nk nw w w' r r';
    finish rn nk nw w w' r r'

/// ---------------------------------------------------------------------------
/// Major allocations
/// ---------------------------------------------------------------------------

let alloc_addr (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) : GTot nat =
  let (_, _, res) = c.a.alloc x.ph x.w.cmaj x.ast sz tag in
  match res with Ok o -> o | NoRoom -> 0

let malloc_cw (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value)
  : Lemma (requires alloc_succeeds x (EAlloc sz tag vs))
          (ensures (step c x (EAlloc sz tag vs)).w.croots == VPtr (Major (alloc_addr x sz tag)) :: x.w.croots /\
                   (step c x (EAlloc sz tag vs)).w.cyng == x.w.cyng)
  = let (_, _, Ok o) = c.a.alloc x.ph x.w.cmaj x.ast sz tag in ()

/// The new block: (2).
let malloc_new (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EAlloc sz tag vs) rn r)
          (ensures (let o = alloc_addr x sz tag in let x' = step c x (EAlloc sz tag vs) in
                    in_use_c x o == false /\ is_block (mj x') o /\ wz_of (mj x') o == sz /\ tag_of (mj x') o == tag /\
                    (forall (i: nat). i < sz /\ i < L.length vs ==> field (mj x') o i == vidx vs i)))
  = ctx x (EAlloc sz tag vs) rn r;
    let (_, _, Ok o) = c.a.alloc x.ph x.w.cmaj x.ast sz tag in ()

let malloc_fresh (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value) (rn: renaming) (r: rstore) (q: ptr)
  : Lemma (requires sim_pre x (EAlloc sz tag vs) rn r /\ visible (vw x) q)
          (ensures q =!= Major (alloc_addr x sz tag))
  = malloc_new x sz tag vs rn r;
    ctx x (EAlloc sz tag vs) rn r;
    match q with
    | Major o' -> assert (kept x o')
    | Young _ -> ()

let alloc_w_intro (rn: renaming) (w w': world) (r: rstore) (np: ptr) (sz: size_t) (tag: tag_t) (vs: list value)
  : Lemma (requires ip_ctx rn w w' r /\
                    w'.roots == VPtr np :: w.roots /\
                    is_block (ph w' np) (pa np) /\ wz_of (ph w' np) (pa np) == sz /\ tag_of (ph w' np) (pa np) == tag /\
                    (forall (i: nat). i < sz ==> fld w' np i == vidx vs i) /\
                    (forall (q: ptr). visible w q ==> q =!= np) /\
                    tag <> infix_tag /\ L.length vs == sz /\
                    (scannable tag ==> (forall (i: nat). i < sz ==> value_ok w (vidx vs i))) /\
                    (forall (p: ptr) (j: nat). visible w p /\ j < wz_of (ph w p) (pa p) ==> fld w' p j == fld w p j) /\
                    (forall (y i: nat) (q: ptr). ptr_field w'.yng y i /\ target w' (field w'.yng y i) == Some q /\ Major? q ==>
                       img w pid (Some np) q))
          (ensures alloc_w rn w w' r np sz tag vs)
  = ()

let mal_core (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EAlloc sz tag vs) rn r)
          (ensures (let o = alloc_addr x sz tag in
                    let w = vw x in let w' = vw (step c x (EAlloc sz tag vs)) in
                    w'.roots == VPtr (Major o) :: w.roots /\ agree w.yng w'.yng /\
                    uc w'.maj /\ uc w'.yng /\ r_res w /\ scorr_w rn w r /\ clean rn w r /\ rwf r))
  = let e = EAlloc sz tag vs in
    let x' = step c x e in
    ctx x e rn r;
    malloc_cw x sz tag vs;
    yng_same x x'

let mal_blk (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EAlloc sz tag vs) rn r)
          (ensures (let o = alloc_addr x sz tag in
                    let w' = vw (step c x (EAlloc sz tag vs)) in
                    is_block w'.maj o /\ wz_of w'.maj o == sz /\ tag_of w'.maj o == tag /\
                    (forall (i: nat). i < sz ==> field w'.maj o i == vidx vs i)))
  = let e = EAlloc sz tag vs in
    malloc_new x sz tag vs rn r;
    vw_views x;
    assert (mutator_ok_w c (vw x) e);
    assert (L.length vs == sz)

let mal_vals (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value)
  : Lemma (requires mutator_ok x (EAlloc sz tag vs))
          (ensures tag <> infix_tag /\ L.length vs == sz /\
                   (scannable tag ==> (forall (i: nat). i < sz ==> value_ok (vw x) (vidx vs i))))
  = assert (mutator_ok_w c (vw x) (EAlloc sz tag vs))

let mal_pre (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EAlloc sz tag vs) rn r)
          (ensures (let o = alloc_addr x sz tag in
                    let w = vw x in let w' = vw (step c x (EAlloc sz tag vs)) in
                    w'.roots == VPtr (Major o) :: w.roots /\ agree w.yng w'.yng /\
                    uc w'.maj /\ uc w'.yng /\ r_res w /\ scorr_w rn w r /\ clean rn w r /\ rwf r /\
                    tag <> infix_tag /\ L.length vs == sz /\
                    (scannable tag ==> (forall (i: nat). i < sz ==> value_ok w (vidx vs i))) /\
                    is_block w'.maj o /\ wz_of w'.maj o == sz /\ tag_of w'.maj o == tag /\
                    (forall (i: nat). i < sz ==> field w'.maj o i == vidx vs i)))
  = let e = EAlloc sz tag vs in
    let x' = step c x e in
    mal_core x sz tag vs rn r;
    mal_vals x sz tag vs;
    mal_blk x sz tag vs rn r

let mal_vis (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EAlloc sz tag vs) rn r)
          (ensures (let w = vw x in let w' = vw (step c x (EAlloc sz tag vs)) in
                    ip_ctx rn w w' r /\
                    (forall (q: ptr). visible w q ==> q =!= Major (alloc_addr x sz tag)) /\
                    (forall (p: ptr) (j: nat). visible w p /\ j < wz_of (ph w p) (pa p) ==> fld w' p j == fld w p j)))
  = let e = EAlloc sz tag vs in
    let x' = step c x e in
    mal_pre x sz tag vs rn r;
    ip_of x e rn r;
    C.forall_intro (C.move_requires (malloc_fresh x sz tag vs rn r));
    C.forall_intro_2 (fun (p: ptr) (j: nat) -> C.move_requires (flds_same x e rn r p) j)

let malloc_world (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EAlloc sz tag vs) rn r)
          (ensures alloc_w rn (vw x) (vw (step c x (EAlloc sz tag vs))) r (Major (alloc_addr x sz tag)) sz tag vs)
  = let e = EAlloc sz tag vs in
    let x' = step c x e in
    let w = vw x in
    let w' = vw x' in
    let np = Major (alloc_addr x sz tag) in
    mal_pre x sz tag vs rn r;
    mal_vis x sz tag vs rn r;
    yrefs_same rn (Some np) w w' r;
    alloc_w_intro rn w w' r np sz tag vs

/// **A major allocation.**
let sim_malloc (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EAlloc sz tag vs) rn r) (ensures sim_post x (EAlloc sz tag vs) rn r)
  = let e = EAlloc sz tag vs in
    let x' = step c x e in
    let w = vw x in
    malloc_world x sz tag vs rn r;
    alloc_ref rn w (vw x') r (Major (alloc_addr x sz tag)) false sz tag vs;
    let re = RAlloc false tag (gmap (trv rn w r (scannable tag)) vs) in
    assert (ev_corr rn w r e re);
    eliminate exists (rn': renaming). scorr_w rn' (vw x') (rstep r re) /\ clean rn' (vw x') (rstep r re)
    with post_mut x e rn r re rn'

/// ---------------------------------------------------------------------------
/// Young allocations
/// ---------------------------------------------------------------------------

let yalloc_addr (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value) : GTot nat =
  match c.r.yalloc x.w.cyng sz tag vs with Some (o, _) -> o | None -> 0

/// The nursery after a young allocation.
let yalloc_yng (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EYoungAlloc sz tag vs) rn r)
          (ensures (let o = yalloc_addr x sz tag vs in let x' = step c x (EYoungAlloc sz tag vs) in
                    young_free (vw x).yng o sz /\ agree (young_alloc (vw x).yng o sz tag vs) (vw x').yng /\
                    (vw x').roots == VPtr (Young o) :: (vw x).roots))
  = let e = EYoungAlloc sz tag vs in
    let x' = step c x e in
    step_ok x e;
    vw_views x;
    vw_views x';
    assert (mutator_ok_w c (vw x) e);
    let Some (o, y2) = c.r.yalloc x.w.cyng sz tag vs in
    assert (young_free (vw x).yng o sz /\ c.r.yrepr (young_alloc (vw x).yng o sz tag vs) y2);
    yrepr_agree c.r (young_alloc (vw x).yng o sz tag vs) (vw x').yng y2

let ya_keep (w w': world) (o: nat) (sz: size_t) (tag: tag_t) (vs: list value) (y: nat)
  : Lemma (requires young_ok w.yng /\ young_free w.yng o sz /\ L.length vs == sz /\
                    agree (young_alloc w.yng o sz tag vs) w'.yng /\ is_block w.yng y)
          (ensures y <> o /\ shape_keep w.yng w'.yng y y /\
                   (forall (j: nat). j < wz_of w.yng y ==> field w'.yng y j == field w.yng y j))
  = let m = young_alloc w.yng o sz tag vs in
    yalloc_keeps w.yng o sz tag vs y;
    ag_hd m w'.yng y;
    C.forall_intro (C.move_requires (ag_field m w'.yng y))

let ya_new (w w': world) (o: nat) (sz: size_t) (tag: tag_t) (vs: list value)
  : Lemma (requires young_free w.yng o sz /\ L.length vs == sz /\ agree (young_alloc w.yng o sz tag vs) w'.yng)
          (ensures is_block w'.yng o /\ wz_of w'.yng o == sz /\ tag_of w'.yng o == tag /\
                   (forall (i: nat). i < sz ==> field w'.yng o i == vidx vs i))
  = let m = young_alloc w.yng o sz tag vs in
    yalloc_new_field w.yng o sz tag vs 0;
    ag_hd m w'.yng o;
    let f (i: nat) : Lemma (i < sz ==> field w'.yng o i == vidx vs i)
      = if i < sz then begin yalloc_new_field w.yng o sz tag vs i; ag_field m w'.yng o i end in
    C.forall_intro f

/// The nursery's major pointers after a young allocation.
let ya_field (w w': world) (o: nat) (sz: size_t) (tag: tag_t) (vs: list value) (y i: nat)
  : Lemma (requires young_ok w.yng /\ young_free w.yng o sz /\ L.length vs == sz /\
                    agree (young_alloc w.yng o sz tag vs) w'.yng /\ ptr_field w'.yng y i)
          (ensures (y == o /\ i < sz /\ scannable tag /\ field w'.yng y i == vidx vs i) \/
                   (y <> o /\ ptr_field w.yng y i /\ field w'.yng y i == field w.yng y i))
  = let m = young_alloc w.yng o sz tag vs in
    agree_sym m w'.yng;
    ag_hd w'.yng m y;
    if y = o then ya_new w w' o sz tag vs
    else begin
      assert (is_block w.yng y);
      ya_keep w w' o sz tag vs y
    end

/// The nursery's major pointers after a young allocation.
let ya_yref (rn: renaming) (w w': world) (r: rstore) (o: nat) (sz: size_t) (tag: tag_t) (vs: list value)
    (y i: nat) (q: ptr)
  : Lemma (requires ip_ctx rn w w' r /\ r_res w /\ young_ok w.yng /\ young_free w.yng o sz /\ L.length vs == sz /\
                    agree (young_alloc w.yng o sz tag vs) w'.yng /\
                    (scannable tag ==> (forall (i: nat). i < sz ==> value_ok w (vidx vs i))) /\
                    ptr_field w'.yng y i /\ target w' (field w'.yng y i) == Some q /\ Major? q)
          (ensures img w pid (Some (Young o)) q)
  = ya_field w w' o sz tag vs y i;
    let u = field w'.yng y i in
    if y = o then begin
      assert (value_ok w u);
      maj_target rn w w' r (Some (Young o)) u q
    end else begin
      res_yng w y i;
      let aux (q0: ptr) : Lemma (requires target w u == Some q0) (ensures visible w q0)
        = vis_young w y i q0 in
      C.forall_intro (C.move_requires aux);
      maj_target rn w w' r (Some (Young o)) u q
    end

let ya_pre (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EYoungAlloc sz tag vs) rn r)
          (ensures (let o = yalloc_addr x sz tag vs in
                    let w = vw x in let w' = vw (step c x (EYoungAlloc sz tag vs)) in
                    young_free w.yng o sz /\ agree (young_alloc w.yng o sz tag vs) w'.yng /\
                    w'.roots == VPtr (Young o) :: w.roots /\
                    young_ok w.yng /\ uc w'.maj /\ uc w'.yng /\ r_res w /\ scorr_w rn w r /\ clean rn w r /\ rwf r /\
                    tag <> infix_tag /\ L.length vs == sz /\
                    (scannable tag ==> (forall (i: nat). i < sz ==> value_ok w (vidx vs i)))))
  = let e = EYoungAlloc sz tag vs in
    yalloc_yng x sz tag vs rn r;
    ctx x e rn r;
    assert (mutator_ok_w c (vw x) e)

let ya_shape (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value) (rn: renaming) (r: rstore) (q: ptr)
  : Lemma (requires sim_pre x (EYoungAlloc sz tag vs) rn r /\ young_ok (vw x).yng /\
                    young_free (vw x).yng (yalloc_addr x sz tag vs) sz /\ L.length vs == sz /\
                    agree (young_alloc (vw x).yng (yalloc_addr x sz tag vs) sz tag vs) (vw (step c x (EYoungAlloc sz tag vs))).yng /\
                    visible (vw x) q)
          (ensures (let w = vw x in let w' = vw (step c x (EYoungAlloc sz tag vs)) in
                    shape_keep (ph w q) (ph w' q) (pa q) (pa q) /\ q =!= Young (yalloc_addr x sz tag vs) /\
                    (forall (j: nat). j < wz_of (ph w q) (pa q) ==> fld w' q j == fld w q j)))
  = let e = EYoungAlloc sz tag vs in
    let w = vw x in
    let w' = vw (step c x e) in
    match q with
    | Major o' ->
      ctx x e rn r;
      maj_vis x e o';
      assert (forall (j: nat). j < wz_of w.maj o' ==> field (mj (step c x e)) o' j == new_field x e o' j)
    | Young y -> yvis_block w y; ya_keep w w' (yalloc_addr x sz tag vs) sz tag vs y

let ya_world (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EYoungAlloc sz tag vs) rn r)
          (ensures alloc_w rn (vw x) (vw (step c x (EYoungAlloc sz tag vs))) r (Young (yalloc_addr x sz tag vs)) sz tag vs)
  = let e = EYoungAlloc sz tag vs in
    let w = vw x in
    let w' = vw (step c x e) in
    let o = yalloc_addr x sz tag vs in
    ya_pre x sz tag vs rn r;
    C.forall_intro (C.move_requires (ya_shape x sz tag vs rn r));
    assert (ip_ctx rn w w' r);
    ya_new w w' o sz tag vs;
    C.forall_intro_3 (fun (y i: nat) (q: ptr) -> C.move_requires (ya_yref rn w w' r o sz tag vs y i) q)

/// **A young allocation.**
let sim_yalloc (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x (EYoungAlloc sz tag vs) rn r) (ensures sim_post x (EYoungAlloc sz tag vs) rn r)
  = let e = EYoungAlloc sz tag vs in
    let x' = step c x e in
    let w = vw x in
    ya_world x sz tag vs rn r;
    alloc_ref rn w (vw x') r (Young (yalloc_addr x sz tag vs)) true sz tag vs;
    let re = RAlloc true tag (gmap (trv rn w r (scannable tag)) vs) in
    assert (ev_corr rn w r e re);
    eliminate exists (rn': renaming). scorr_w rn' (vw x') (rstep r re) /\ clean rn' (vw x') (rstep r re)
    with post_mut x e rn r re rn'
