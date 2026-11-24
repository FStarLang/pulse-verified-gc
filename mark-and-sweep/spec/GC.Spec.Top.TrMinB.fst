/// ---------------------------------------------------------------------------
/// GC.Spec.Top.TrMinB - the correspondence across a minor collection
/// ---------------------------------------------------------------------------
///
/// Design doc §16.15.  From the collection's contract (through
/// GC.Spec.Top.StepMinor): a visible young block is traced (`ymlive`), so
/// copied; a visible major block is one the program may use, so kept with
/// its young pointers forwarded; the roots are forwarded; the nursery is
/// emptied (`mctx_of`).  A collection out of room changes no world
/// (`sim_oor`).

module GC.Spec.Top.TrMinB

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
open GC.Spec.Top.TrMinA
open GC.Spec.Top.StepMinor
module L = FStar.List.Tot
module C = FStar.Classical
module ID = FStar.IndefiniteDescription

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Visible young blocks are traced
/// ---------------------------------------------------------------------------

let mlived (w: world) (y: nat) (m: mlive w y) : Lemma (minor_live w y)
  = C.exists_intro (fun (_: mlive w y) -> True) m

let get_mlive (w: world) (y: nat) : Ghost (mlive w y) (requires minor_live w y) (ensures fun _ -> True)
  = ID.indefinite_description_ghost (mlive w y) (fun _ -> True)

let old_slot (#c: comps) (x: config c) (o i a: nat)
  : Lemma (requires rinv x /\ reachable (vw x) o /\ ptr_field (vw x).maj o i /\ field (vw x).maj o i == VPtr (Young a))
          (ensures L.memP (o, i) (vw x).rem)
  = n_kept_lt x o;
    reveal_opaque (`%r_young) (r_young #c)

let rec ymlive (#c: comps) (x: config c) (y: nat) (r: yreach (vw x) y)
  : Lemma (requires rinv x) (ensures minor_live (vw x) y) (decreases r)
  = let w = vw x in
    match r with
    | YRoot _ a _ -> mlived w y (LRoot y a ())
    | YOld _ o i a r0 _ ->
      reached w o r0;
      old_slot x o i a;
      mlived w y (LRem y o i a ())
    | YStep y0 _ r0 _ ->
      ymlive x y0 r0;
      mlived w y (LStep y0 y (get_mlive w y0) ())

/// ---------------------------------------------------------------------------
/// The collection's facts, for the reference side
/// ---------------------------------------------------------------------------

let mp_inj (#c: comps) (x: config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) (y1 y2: nat)
  : Lemma (requires mpost x hc' st' roots' fwd m' /\ fwd y1 == fwd y2 /\ Some? (fwd y1)) (ensures y1 == y2)
  = reveal_opaque (`%mpost) (mpost #c)

let ag_shape (h m m': mheap) (o o': nat)
  : Lemma (requires shape_keep h m o o' /\ agree m m') (ensures shape_keep h m' o o')
  = ag_hd m m' o';
    C.forall_intro (C.move_requires (ag_field m m' o'))

/// A visible major block stays, its young pointers forwarded.
let mx_maj (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) (t: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ reachable (vw x) t)
          (ensures shape_keep (mj x) m' t t /\
                   (forall (j: nat). j < wz_of (mj x) t ==> field m' t j == fwd_field (mj x) t j (vw x).yng fwd))
  = n_kept_lt x t;
    n_keepsy x x' hc' st' roots' fwd m' t;
    n_wf x x' hc' st' roots' fwd m';
    mp_old x hc' st' roots' fwd m' t

/// A visible young block is copied.
let mx_yng (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) (y: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ yreachable (vw x) y)
          (ensures Some? (fwd y) /\ shape_keep (vw x).yng m' y (Some?.v (fwd y)) /\
                   (forall (j: nat). j < wz_of (vw x).yng y ==>
                      field m' (Some?.v (fwd y)) j == fwd_field (vw x).yng y j (vw x).yng fwd) /\
                   ~(in_use_c x (Some?.v (fwd y))))
  = yvis_block (vw x) y;
    ymlive x y (get_yreach (vw x) y);
    mp_fwd x hc' st' roots' fwd m' y;
    let cp = Some?.v (fwd y) in
    n_copy x x' hc' st' roots' fwd m' y cp;
    mp_copy x hc' st' roots' fwd m' y cp

/// The same, in the view of the next configuration.
let mx_shapes (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) (w': world) (p: ptr) (j: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ agree m' w'.maj /\ visible (vw x) p)
          (ensures (match p with
                    | Major t -> shape_keep (mj x) w'.maj t t
                    | Young y -> Some? (fwd y) /\ shape_keep (vw x).yng w'.maj y (Some?.v (fwd y))) /\
                   (j < wz_of (ph (vw x) p) (pa p) ==>
                      fld w' (fmu fwd p) j == fwd_field (ph (vw x) p) (pa p) j (vw x).yng fwd))
  = match p with
    | Major t ->
      mx_maj x x' hc' st' roots' fwd m' t;
      ag_shape (mj x) m' w'.maj t t;
      if j < wz_of (mj x) t then ag_field m' w'.maj t j
    | Young y ->
      mx_yng x x' hc' st' roots' fwd m' y;
      let cp = Some?.v (fwd y) in
      ag_shape (vw x).yng m' w'.maj y cp;
      if j < wz_of (vw x).yng y then ag_field m' w'.maj cp j

let mx_cross (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) (t y: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ reachable (vw x) t /\ yreachable (vw x) y)
          (ensures fwd y =!= Some t)
  = n_kept_lt x t;
    mx_yng x x' hc' st' roots' fwd m' y

let empty_no_block (m m': mheap) (y: nat)
  : Lemma (requires agree (empty_heap m.size) m') (ensures ~(is_block m' y))
  = agree_sym (empty_heap m.size) m';
    if is_block m' y then ag_hd m' (empty_heap m.size) y

/// **The collection's facts.**
let mctx_of (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) (rn: renaming) (r: rstore) (w': world)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ scorr_w rn (vw x) r /\ clean rn (vw x) r /\ rwf r /\
                    wagree (wnext x fwd m') w')
          (ensures mctx rn (vw x) w' r fwd)
  = let w = vw x in
    n_wf x x' hc' st' roots' fwd m';
    ag_well_formed m' w'.maj;
    C.forall_intro_2 (fun (p: ptr) (j: nat) -> C.move_requires (mx_shapes x x' hc' st' roots' fwd m' w' p) j);
    let f (t: nat) : Lemma (reachable w t ==> shape_keep w.maj w'.maj t t)
      = if ID.strong_excluded_middle (reachable w t) then mx_shapes x x' hc' st' roots' fwd m' w' (Major t) 0 in
    let g (y: nat) : Lemma (yreachable w y ==> Some? (fwd y) /\ shape_keep w.yng w'.maj y (Some?.v (fwd y)))
      = if ID.strong_excluded_middle (yreachable w y) then mx_shapes x x' hc' st' roots' fwd m' w' (Young y) 0 in
    C.forall_intro f;
    C.forall_intro g;
    C.forall_intro (empty_no_block w.yng w'.yng);
    C.forall_intro_2 (fun (y1 y2: nat) -> C.move_requires (mp_inj x hc' st' roots' fwd m' y1) y2);
    C.forall_intro_2 (fun (t y: nat) -> C.move_requires (mx_cross x x' hc' st' roots' fwd m' t) y);
    mp_basic x hc' st' roots' fwd m'

/// ---------------------------------------------------------------------------
/// The step
/// ---------------------------------------------------------------------------

let done_world (#c: comps) (x: config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
  : Lemma (requires faithful c.r /\ rinv x /\ hyps_at c x EMinor /\ c.n.collect x.ph x.ast x.w == Done hc' st' roots' fwd)
          (ensures exists (m': mheap). mok x (step c x EMinor) hc' st' roots' fwd m' /\
                                      wagree (wnext x fwd m') (vw (step c x EMinor)))
  = let x' = step c x EMinor in
    let w = vw x in
    vw_views x;
    minor_pre_of x;
    assert (minor_m c.r c.n x.ph x.ast x.w w);
    let m' = ID.indefinite_description_ghost mheap
               (fun m' -> c.r.repr m' hc' /\ minor_post_done c.a x.ph x.ast x.w.cmaj w hc' st' roots' fwd m') in
    reveal_opaque (`%mpost) (mpost #c);
    assert (mpost x hc' st' roots' fwd m');
    assert (c.r.yrepr (empty_heap w.yng.size) (c.r.yreset x.w.cyng));
    minor_next x hc' st' roots' fwd;
    assert (mok x x' hc' st' roots' fwd m');
    mp_basic x hc' st' roots' fwd m';
    assert (views x' (wnext x fwd m'));
    vw_agree x' (wnext x fwd m')

/// **A minor collection that succeeds.**
let sim_done (#c: comps) (x: config c) (rn: renaming) (r: rstore) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat)
  : Lemma (requires sim_pre x EMinor rn r /\ c.n.collect x.ph x.ast x.w == Done hc' st' roots' fwd)
          (ensures sim_post x EMinor rn r)
  = let x' = step c x EMinor in
    scorr_eq rn x r;
    done_world x hc' st' roots' fwd;
    eliminate exists (m': mheap). mok x x' hc' st' roots' fwd m' /\ wagree (wnext x fwd m') (vw x')
    with begin
      mctx_of x x' hc' st' roots' fwd m' rn r (vw x');
      minor_ref rn (vw x) (vw x') r fwd;
      post_of x' r
    end

let oor_vis (#c: comps) (x: config c) (w': world) (p: ptr) (j: nat)
  : Lemma (requires rinv x /\ wagree (vw x) w' /\ visible (vw x) p)
          (ensures shape_keep (ph (vw x) p) (ph w' p) (pa p) (pa p) /\
                   (j < wz_of (ph (vw x) p) (pa p) ==> fld w' p j == fld (vw x) p j))
  = let w = vw x in
    match p with
    | Major t ->
      reach_kept x w t;
      agree_refl w.maj;
      ag_shape w.maj w.maj w'.maj t t;
      if j < wz_of w.maj t then ag_field w.maj w'.maj t j
    | Young y ->
      yvis_block w y;
      agree_refl w.yng;
      ag_shape w.yng w.yng w'.yng y y;
      if j < wz_of w.yng y then ag_field w.yng w'.yng y j

let oor_basic (#c: comps) (x: config c) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x EMinor rn r /\ c.n.collect x.ph x.ast x.w == OutOfRoom)
          (ensures (let w = vw x in let w' = vw (step c x EMinor) in
                    wagree w w' /\ uc w'.maj /\ uc w'.yng /\ r_res w /\ scorr_w rn w r /\ clean rn w r /\ rwf r /\
                    rinv x))
  = let x' = step c x EMinor in
    ctx x EMinor rn r;
    assert (views x' (vw x));
    vw_agree x' (vw x)

let ip_intro (rn: renaming) (w w': world) (r: rstore)
  : Lemma (requires scorr_w rn w r /\ clean rn w r /\ rwf r /\ uc w'.maj /\ uc w'.yng /\
                    (forall (q: ptr). visible w q ==> shape_keep (ph w q) (ph w' q) (pa q) (pa q)))
          (ensures ip_ctx rn w w' r)
  = ()

let oor_world (#c: comps) (x: config c) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x EMinor rn r /\ c.n.collect x.ph x.ast x.w == OutOfRoom)
          (ensures (let w = vw x in let w' = vw (step c x EMinor) in
                    same_w rn w w' r /\ w'.roots == w.roots /\ scorr_w rn w r))
  = let w = vw x in
    let w' = vw (step c x EMinor) in
    oor_basic x rn r;
    let f (q: ptr) : Lemma (visible w q ==> shape_keep (ph w q) (ph w' q) (pa q) (pa q))
      = if ID.strong_excluded_middle (visible w q) then oor_vis x w' q 0 in
    C.forall_intro f;
    ip_intro rn w w' r;
    C.forall_intro_2 (fun (p: ptr) (j: nat) -> C.move_requires (oor_vis x w' p) j)

/// What a step that changes no visible word leaves: the same store.
let same_ref (rn: renaming) (w w': world) (r: rstore)
  : Lemma (requires same_w rn w w' r /\ w'.roots == w.roots)
          (ensures exists (rn': renaming). scorr_w rn' w' r /\ clean rn' w' r)
  = roots_same rn r.next None w w' r;
    yrefs_same rn None w w' r;
    objs_same rn r.next None w w' r r;
    finish rn r.next None w w' r r

/// **A minor collection out of room**: no world changes.
let sim_oor (#c: comps) (x: config c) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x EMinor rn r /\ c.n.collect x.ph x.ast x.w == OutOfRoom)
          (ensures sim_post x EMinor rn r)
  = let x' = step c x EMinor in
    oor_world x rn r;
    same_ref rn (vw x) (vw x') r;
    post_of x' r

/// **A minor collection.**
let sim_minor (#c: comps) (x: config c) (rn: renaming) (r: rstore)
  : Lemma (requires sim_pre x EMinor rn r) (ensures sim_post x EMinor rn r)
  = match c.n.collect x.ph x.ast x.w with
    | OutOfRoom -> sim_oor x rn r
    | Done hc' st' roots' fwd -> sim_done x rn r hc' st' roots' fwd
