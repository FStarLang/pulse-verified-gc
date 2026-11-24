/// ---------------------------------------------------------------------------
/// GC.Spec.Top.TrEvA - the correspondence across collector steps, reads and
/// root changes: the common part
/// ---------------------------------------------------------------------------
///
/// Design doc §16.15.  `sim_pre`/`sim_post`: what one step needs and gives.
/// Steps other than a minor collection keep the contents of every kept
/// major block ((1a)); visible blocks are kept, so with the nursery kept
/// they stay in place (`ip_of`).

module GC.Spec.Top.TrEvA

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
module L = FStar.List.Tot
module C = FStar.Classical
module ID = FStar.IndefiniteDescription

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// One step
/// ---------------------------------------------------------------------------

let sim_pre (#c: comps) (x: config c) (e: event) (rn: renaming) (r: rstore) : prop =
  faithful c.r /\ rinv x /\ hyps_at c x e /\ enabled c x e /\ mutator_ok x e /\ alloc_succeeds x e /\
  scorr rn x r /\ clean rn (wv x) r /\ rwf r

let sim_post (#c: comps) (x: config c) (e: event) (rn: renaming) (r: rstore) : prop =
  let x' = step c x e in
  if is_mutator_event e then
    (exists (re: revent) (rn': renaming).
       rok r re /\ ev_corr rn (wv x) r e re /\ scorr rn' x' (rstep r re) /\ clean rn' (wv x') (rstep r re))
  else (exists (rn': renaming). scorr rn' x' r /\ clean rn' (wv x') r)

/// The facts every step gives.
let ctx (#c: comps) (x: config c) (e: event) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x e rn r)
          (ensures (let x' = step c x e in
                    rinv x' /\ concl_step x e x' /\ concl_point x /\ concl_point x' /\
                    views x (vw x) /\ views x' (vw x') /\ (vw x).roots == x.w.croots /\ (vw x').roots == x'.w.croots /\
                    uc (vw x').maj /\ uc (vw x').yng /\ r_res (vw x) /\ scorr_w rn (vw x) r))
  = let x' = step c x e in
    step_ok x e;
    point_of_rinv x;
    point_of_rinv x';
    vw_views x;
    vw_views x';
    scorr_eq rn x r

/// The rest of a step: the general step, then cut down.
let finish (rn: renaming) (nk: nat) (nw: option ptr) (w w': world) (r r': rstore)
  : Lemma (requires gen_hyps rn pid nk nw w w' r r' /\ rwf r')
          (ensures exists (rn': renaming). scorr_w rn' w' r' /\ clean rn' w' r')
  = sim_gen rn pid nk nw w w' r r';
    restrict_scorr (rn_step rn pid nk nw) w' r'

/// ---------------------------------------------------------------------------
/// Visible blocks
/// ---------------------------------------------------------------------------

let yvis_block (w: world) (y: nat) : Lemma (requires yreachable w y) (ensures is_block w.yng y)
  = match get_yreach w y with
    | YRoot _ a _ -> resolve_block w.yng a y
    | YOld _ _ _ a _ _ -> resolve_block w.yng a y
    | YStep y0 _ _ _ ->
      eliminate exists (i a: nat). ptr_field w.yng y0 i /\ field w.yng y0 i == VPtr (Young a) /\ resolve w.yng a == Some y
      with resolve_block w.yng a y

/// The fields a step leaves a kept major block: the program's write, or
/// the old ones.
let new_field (#c: comps) (x: config c) (e: event) (o j: nat) : GTot value =
  match e with
  | EWrite (Major t) i v -> if o = t && j = i then v else field (mj x) o j
  | _ -> field (mj x) o j

/// A visible major block is kept: in use, with its contents ((1a)).
let maj_vis (#c: comps) (x: config c) (e: event) (o: nat)
  : Lemma (requires concl_point x /\ concl_step x e (step c x e) /\ reachable (vw x) o /\ ~(EMinor? e) /\
                    (match e with EWrite (Major t) _ _ -> tag_of (mj x) t <> closure_tag | _ -> True))
          (ensures (let x' = step c x e in
                    shape_keep (mj x) (mj x') o o /\
                    (forall (j: nat). j < wz_of (mj x) o ==> field (mj x') o j == new_field x e o j)))
  = let x' = step c x e in
    assert (kept x o);
    assert (in_use_c x' o == true /\ contents_step x e x' o)

/// The nursery kept: its blocks stay, with their fields.
let yng_agree_keep (w w': world) (y: nat)
  : Lemma (requires agree w.yng w'.yng /\ is_block w.yng y)
          (ensures shape_keep w.yng w'.yng y y /\ (forall (j: nat). j < wz_of w.yng y ==> field w'.yng y j == field w.yng y j))
  = ag_hd w.yng w'.yng y;
    C.forall_intro (C.move_requires (ag_field w.yng w'.yng y))

/// **A step that keeps the nursery keeps every visible block in place.**
let ip_of (#c: comps) (x: config c) (e: event) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x e rn r /\ ~(EMinor? e) /\ agree (vw x).yng (vw (step c x e)).yng /\
                    (match e with EWrite (Major t) _ _ -> tag_of (mj x) t <> closure_tag | _ -> True))
          (ensures ip_ctx rn (vw x) (vw (step c x e)) r)
  = ctx x e rn r;
    let w = vw x in
    let w' = vw (step c x e) in
    let f (q: ptr) : Lemma (requires visible w q) (ensures shape_keep (ph w q) (ph w' q) (pa q) (pa q))
      = match q with
        | Major o -> maj_vis x e o
        | Young y -> yvis_block w y; yng_agree_keep w w' y in
    C.forall_intro (C.move_requires f)

/// The words of every visible block, below its size, after a step that
/// keeps the nursery and writes no major block.
let flds_same (#c: comps) (x: config c) (e: event) (rn: renaming) (r: rstore) (p: ptr) (j: nat)
  : Lemma (requires sim_pre x e rn r /\ ~(EMinor? e) /\ ~(EWrite? e) /\ agree (vw x).yng (vw (step c x e)).yng /\
                    visible (vw x) p /\ j < wz_of (ph (vw x) p) (pa p))
          (ensures fld (vw (step c x e)) p j == fld (vw x) p j)
  = ctx x e rn r;
    let w = vw x in
    let w' = vw (step c x e) in
    match p with
    | Major o -> maj_vis x e o
    | Young y -> yvis_block w y; yng_agree_keep w w' y

/// ---------------------------------------------------------------------------
/// Pieces
/// ---------------------------------------------------------------------------

/// The old roots keep their correspondence.
let root_keep (rn: renaming) (nk: nat) (nw: option ptr) (w w': world) (r: rstore) (j: nat)
  : Lemma (requires ip_ctx rn w w' r /\ (Some? nw ==> nk == r.next) /\ j < L.length w.roots)
          (ensures vcorr (rn_step rn pid nk nw) w' true (L.index w.roots j) (L.index r.rroots j))
  = let v = L.index w.roots j in
    let rv = L.index r.rroots j in
    assert (vcorr rn w true v rv);
    idx_memP w.roots j;
    match rv with
    | RPtr k d ->
      vcorr_ptr rn w true v k d;
      let q = Some?.v (rn k) in
      vis_root w v q;
      name_ok rn w r k q;
      C.forall_intro (C.move_requires (vis_root w v));
      vmoved_id rn w w' r v;
      vcorr_move rn pid nk nw w w' true v v rv
    | RWord _ -> vcorr_move rn pid nk nw w w' true v v rv

let roots_same (rn: renaming) (nk: nat) (nw: option ptr) (w w': world) (r: rstore)
  : Lemma (requires ip_ctx rn w w' r /\ (Some? nw ==> nk == r.next) /\ w'.roots == w.roots)
          (ensures roots_corr (rn_step rn pid nk nw) w' r)
  = let f (j: nat) : Lemma (j < L.length w.roots ==>
                            vcorr (rn_step rn pid nk nw) w' true (L.index w.roots j) (L.index r.rroots j))
      = if j < L.length w.roots then root_keep rn nk nw w w' r j in
    C.forall_intro f

/// A new root in front of the old ones.
let roots_push (rn: renaming) (nk: nat) (nw: option ptr) (w w': world) (r r': rstore) (v: value) (rv: rval)
  : Lemma (requires ip_ctx rn w w' r /\ (Some? nw ==> nk == r.next) /\ w'.roots == v :: w.roots /\
                    r'.rroots == rv :: r.rroots /\ vcorr (rn_step rn pid nk nw) w' true v rv)
          (ensures roots_corr (rn_step rn pid nk nw) w' r')
  = let f (j: nat) : Lemma (j < L.length w'.roots ==>
                            vcorr (rn_step rn pid nk nw) w' true (L.index w'.roots j) (L.index r'.rroots j))
      = if j > 0 && j < L.length w'.roots then root_keep rn nk nw w w' r (j - 1) in
    C.forall_intro f

/// The nursery kept: it points only into the visible blocks.
let yref_same (rn: renaming) (nw: option ptr) (w w': world) (r: rstore) (y i: nat) (q: ptr)
  : Lemma (requires ip_ctx rn w w' r /\ agree w.yng w'.yng /\ r_res w /\
                    ptr_field w'.yng y i /\ target w' (field w'.yng y i) == Some q /\ Major? q)
          (ensures img w pid nw q)
  = agree_sym w.yng w'.yng;
    ag_ptr_field w'.yng w.yng y i;
    ag_field w'.yng w.yng y i;
    res_yng w y i;
    let VPtr (Major a) = field w.yng y i in
    let Some o = resolve w.maj a in
    vis_young w y i (Major o);
    ip_keep rn w w' r (Major o);
    resolve_block w.maj a o;
    resolve_move w.maj w'.maj a o o;
    assert (resolve w'.maj a == Some o);
    assert (q == Major o);
    assert (visible w (Major o) /\ q == pid (Major o))

let yrefs_same (rn: renaming) (nw: option ptr) (w w': world) (r: rstore)
  : Lemma (requires ip_ctx rn w w' r /\ agree w.yng w'.yng /\ r_res w)
          (ensures forall (y i: nat) (q: ptr). ptr_field w'.yng y i /\ target w' (field w'.yng y i) == Some q /\ Major? q ==>
                     img w pid nw q)
  = C.forall_intro_3 (fun (y i: nat) (q: ptr) -> C.move_requires (yref_same rn nw w w' r y i) q)

/// Every visible block keeps its fields (below its size) and its object.
let objs_same (rn: renaming) (nk: nat) (nw: option ptr) (w w': world) (r r': rstore)
  : Lemma (requires ip_ctx rn w w' r /\ (Some? nw ==> nk == r.next) /\
                    (forall (k: nat). Some? (rn k) ==> r'.objs k == r.objs k) /\
                    (forall (p: ptr) (j: nat). visible w p /\ j < wz_of (ph w p) (pa p) ==> fld w' p j == fld w p j))
          (ensures forall (k: nat). {:pattern (rn k)}
                     Some? (rn k) ==> Some? (r'.objs k) /\ ocorr (rn_step rn pid nk nw) w' (pid (Some?.v (rn k))) (Some?.v (r'.objs k)))
  = let f (k: nat) : Lemma (Some? (rn k) ==> Some? (r'.objs k) /\
                            ocorr (rn_step rn pid nk nw) w' (pid (Some?.v (rn k))) (Some?.v (r'.objs k)))
      = match rn k with
        | Some p ->
          assert (visible w p);
          name_ocorr rn w r k p;
          ocorr_keep rn nk nw w w' r k p (robj_of r k)
        | None -> () in
    C.forall_intro f
