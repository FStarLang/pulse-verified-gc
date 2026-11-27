/// ---------------------------------------------------------------------------
/// GC.Spec.Top.StepMinor - a minor collection
/// ---------------------------------------------------------------------------
///
/// Design doc §16.6 (module 9): `EMinor`, clause (3d).
///   - Its precondition holds (`minor_pre_of`): the remembered set covers
///     the blocks the program may use (R4), the nursery's major pointers
///     have kept targets (R3), its young pointers resolve.
///   - Every young pointer that matters resolves to an object the
///     collection traces, so it is forwarded to a copy (`fv`): a root
///     (`LRoot`), a field of a block the program may use (it is remembered,
///     `LRem`), a field of a traced young object (`LStep`).  A forwarded
///     pointer resolves to its copy, infix pointers included (`copy_resolve`).
///     So after the reset no young pointer is left in a root, a reachable
///     block or a block the program may use.
///   - Blocks the program may use keep their header and every field that is
///     not a young pointer (`keepsy`), so their pointers resolve as before;
///     the copies are new, in use, allocated in the cycle, coloured by
///     `colour_at`.  Reachable after: reachable before, or a copy.
///   - While marking, paths from live grey blocks survive (`lpath_keepy`) and
///     the copies are black.

module GC.Spec.Top.StepMinor

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Views
open GC.Spec.Top.Words
open GC.Spec.Top.RInv
open GC.Spec.Top.StepBase
open GC.Spec.Top.StepFacts
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module C = FStar.Classical

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

let is_copy (fwd: nat -> option nat) (z: nat) : prop = exists (q: nat). fwd q == Some z

/// ---------------------------------------------------------------------------
/// The precondition
/// ---------------------------------------------------------------------------

let ysound1 (#c: comps) (x: config c) (y i b: nat)
  : Lemma (requires rinv x /\ ptr_field (vw x).yng y i /\ field (vw x).yng y i == VPtr (Major b))
          (ensures sound_value c.a x.ph x.ast x.w.cmaj (mj x) (VPtr (Major b)))
  = let w = vw x in
    res_yng w y i;
    let t = Some?.v (resolve w.maj b) in
    reach_young w y i b t;
    reach_kept x w t;
    kept_live_target x w t

let follow1 (#c: comps) (x: config c) (o i a: nat)
  : Lemma (requires rinv x /\ ptr_field (vw x).yng o i /\ field (vw x).yng o i == VPtr (Young a))
          (ensures follow_at (vw x).yng a)
  = res_yng (vw x) o i

/// **The minor collection's precondition, from the invariant.**
let minor_pre_of (#c: comps) (x: config c)
  : Lemma (requires rinv x) (ensures minor_pre c.a x.ph x.ast x.w.cmaj (vw x))
  = reveal_opaque (`%r_heap) (r_heap #c);
    reveal_opaque (`%r_young) (r_young #c);
    C.forall_intro_3 (fun y i b -> C.move_requires (ysound1 x y i) b);
    C.forall_intro_3 (fun o i a -> C.move_requires (follow1 x o i) a)

/// ---------------------------------------------------------------------------
/// The collection's guarantee, sealed
/// ---------------------------------------------------------------------------

[@@"opaque_to_smt"]
let mpost (#c: comps) (x: config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) : prop =
  minor_post_done c.a x.ph x.ast x.w.cmaj (vw x) hc' st' roots' fwd m'

let mp_basic (#c: comps) (x: config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap)
  : Lemma (requires mpost x hc' st' roots' fwd m')
          (ensures m'.size == (mj x).size /\ well_formed m' /\ c.a.inv x.ph hc' st' /\
                   roots' == L.map (fwdv (vw x).yng fwd) (vw x).roots)
  = reveal_opaque (`%mpost) (mpost #c)

let mp_fwd (#c: comps) (x: config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) (q: nat)
  : Lemma (requires mpost x hc' st' roots' fwd m')
          (ensures Some? (fwd q) <==> (is_block (vw x).yng q /\ minor_live (vw x) q))
  = reveal_opaque (`%mpost) (mpost #c)

let mp_copy (#c: comps) (x: config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) (q cp: nat)
  : Lemma (requires mpost x hc' st' roots' fwd m' /\ fwd q == Some cp)
          (ensures m'.hd cp == Some ({ wz = wz_of (vw x).yng q; tag = tag_of (vw x).yng q; col = colour_at c.k x.ph cp }) /\
                   (forall (j: nat). j < wz_of (vw x).yng q ==> field m' cp j == fwd_field (vw x).yng q j (vw x).yng fwd) /\
                   (forall (n: nat). covers m' cp n ==> free_word c.a x.ast x.w.cmaj (mj x) n))
  = reveal_opaque (`%mpost) (mpost #c)

let mp_iu (#c: comps) (x: config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) (z: nat)
  : Lemma (requires mpost x hc' st' roots' fwd m')
          (ensures in_use c.a st' hc' m' z <==> (in_use_c x z \/ is_copy fwd z))
  = reveal_opaque (`%mpost) (mpost #c)

let mp_old (#c: comps) (x: config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) (z: nat)
  : Lemma (requires mpost x hc' st' roots' fwd m' /\ in_use_c x z)
          (ensures m'.hd z == (mj x).hd z /\
                   (live_target c.a x.ph x.ast x.w.cmaj (mj x) z ==>
                      (forall (j: nat). j < wz_of (mj x) z ==> field m' z j == fwd_field (mj x) z j (vw x).yng fwd)))
  = reveal_opaque (`%mpost) (mpost #c)

/// ---------------------------------------------------------------------------
/// The step's context
/// ---------------------------------------------------------------------------

let mok (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) : prop =
  rinv x /\ mpost x hc' st' roots' fwd m' /\
  x'.ph == x.ph /\ x'.ast == st' /\ x'.w.cmaj == hc' /\ x'.w.croots == roots' /\ x'.w.crem == [] /\
  x'.snap == x.snap /\ x'.ms == x.ms /\ (forall (p: nat). x'.allocd p <==> x.allocd p \/ is_copy fwd p)

let wnext (#c: comps) (x: config c) (fwd: nat -> option nat) (m': mheap) : GTot world =
  { maj = m'; yng = empty_heap (vw x).yng.size; roots = L.map (fwdv (vw x).yng fwd) (vw x).roots; rem = [] }

let n_wf (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap)
  : Lemma (requires mok x x' hc' st' roots' fwd m')
          (ensures well_formed (mj x) /\ young_ok (vw x).yng /\ well_formed m' /\ unique_cover m' /\
                   m'.size == (mj x).size)
  = reveal_opaque (`%r_heap) (r_heap #c);
    mp_basic x hc' st' roots' fwd m'

/// A copy is a new block, in use after.
let n_copy (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) (q cp: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ fwd q == Some cp)
          (ensures ~(in_use_c x cp) /\ iu x' m' cp /\ is_block m' cp /\
                   wz_of m' cp == wz_of (vw x).yng q /\ tag_of m' cp == tag_of (vw x).yng q /\
                   col_of m' cp == colour_at c.k x.ph cp)
  = n_wf x x' hc' st' roots' fwd m';
    mp_copy x hc' st' roots' fwd m' q cp;
    mp_iu x hc' st' roots' fwd m' cp;
    assert (covers m' cp cp);
    assert (free_word c.a x.ast x.w.cmaj (mj x) cp);
    if in_use_c x cp then begin
      assert (covers (mj x) cp cp);
      C.forall_intro (C.move_requires (cover_unique (mj x) cp cp))
    end

let n_iu (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) (z: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m')
          (ensures (iu x' m' z <==> (in_use_c x z \/ is_copy fwd z)) /\
                   (in_use_c x z ==> m'.hd z == (mj x).hd z /\ ~(is_copy fwd z)))
  = mp_iu x hc' st' roots' fwd m' z;
    if in_use_c x z then begin
      mp_old x hc' st' roots' fwd m' z;
      let nc (q: nat) : Lemma (~(fwd q == Some z))
        = C.move_requires (n_copy x x' hc' st' roots' fwd m' q) z in
      C.forall_intro nc
    end

/// Forwarding changes only young pointers.
let fwd_nonyoung (y: mheap) (fwd: nat -> option nat) (v: value)
  : Lemma (requires not (is_young v)) (ensures fwdv y fwd v == v)
  = ()

/// A block the program may use is kept up to its young pointers.
let n_keepsy (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) (z: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ live_target c.a x.ph x.ast x.w.cmaj (mj x) z)
          (ensures keepsy (mj x) m' z /\ iu x' m' z /\
                   (forall (j: nat). j < wz_of (mj x) z ==> field m' z j == fwd_field (mj x) z j (vw x).yng fwd))
  = n_wf x x' hc' st' roots' fwd m';
    n_iu x x' hc' st' roots' fwd m' z;
    mp_old x hc' st' roots' fwd m' z;
    let f (j: nat) : Lemma (j < wz_of (mj x) z /\ not (is_young (field (mj x) z j)) ==>
                            field m' z j == field (mj x) z j)
      = if j < wz_of (mj x) z && not (is_young (field (mj x) z j)) then
          fwd_nonyoung (vw x).yng fwd (field (mj x) z j) in
    C.forall_intro f

/// While marking or sweeping, a live block is one the program may use.
let n_live_lt (#c: comps) (x: config c) (z: nat)
  : Lemma (requires rinv x /\ ~(Idle? x.ph) /\ live x z) (ensures live_target c.a x.ph x.ast x.w.cmaj (mj x) z)
  = reveal_opaque (`%r_live) (r_live #c);
    reveal_opaque (`%r_col) (r_col #c);
    match x.ph with
    | Sweeping p -> assert (col_sweep x p (mj x) z)
    | _ -> ()

let n_kept_lt (#c: comps) (x: config c) (z: nat)
  : Lemma (requires rinv x /\ reachable (vw x) z) (ensures live_target c.a x.ph x.ast x.w.cmaj (mj x) z /\ kept x z)
  = reach_kept x (vw x) z;
    kept_live_target x (vw x) z

/// ---------------------------------------------------------------------------
/// Forwarded values
/// ---------------------------------------------------------------------------

/// **A forwarded pointer resolves to its copy**, infix pointers included.
let copy_resolve (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap) (b q cp: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ resolve (vw x).yng b == Some q /\ fwd q == Some cp)
          (ensures resolve m' (cp + (b - q)) == Some cp)
  = let y = (vw x).yng in
    n_wf x x' hc' st' roots' fwd m';
    n_copy x x' hc' st' roots' fwd m' q cp;
    if b = q then ()
    else begin
      mp_copy x hc' st' roots' fwd m' q cp;
      copy_infix y m' fwd b q cp
    end

/// What a value must be for its forwarding to resolve: a major pointer to a
/// block the program may use, or a young pointer to a traced object.
let fwd_ok (#c: comps) (x: config c) (u: value) : prop =
  match u with
  | VPtr (Major a) -> exists (t: nat). resolve (mj x) a == Some t /\ live_target c.a x.ph x.ast x.w.cmaj (mj x) t
  | VPtr (Young b) -> exists (q: nat). resolve (vw x).yng b == Some q /\ minor_live (vw x) q
  | _ -> True

/// Where a forwarded value points.
let fwd_to (#c: comps) (x: config c) (fwd: nat -> option nat) (m': mheap) (u: value) : prop =
  match fwdv (vw x).yng fwd u with
  | VPtr (Young _) -> False
  | VPtr (Major a') ->
    (exists (t: nat). resolve m' a' == Some t /\
       ((u == VPtr (Major a') /\ resolve (mj x) a' == Some t) \/ is_copy fwd t))
  | _ -> True

let fv (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) (u: value)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ fwd_ok x u) (ensures fwd_to x fwd m' u)
  = let y = (vw x).yng in
    match u with
    | VPtr (Major a) ->
      eliminate exists (t: nat). resolve (mj x) a == Some t /\ live_target c.a x.ph x.ast x.w.cmaj (mj x) t
      with begin
        n_keepsy x x' hc' st' roots' fwd m' t;
        n_wf x x' hc' st' roots' fwd m';
        resolve_keepy (mj x) m' a t;
        fwd_nonyoung y fwd u;
        assert (fwdv y fwd u == VPtr (Major a));
        assert (resolve m' a == Some t /\ u == VPtr (Major a) /\ resolve (mj x) a == Some t)
      end
    | VPtr (Young b) ->
      eliminate exists (q: nat). resolve y b == Some q /\ minor_live (vw x) q
      with begin
        resolve_block y b q;
        mp_fwd x hc' st' roots' fwd m' q;
        let cp = Some?.v (fwd q) in
        copy_resolve x x' hc' st' roots' fwd m' b q cp;
        assert (fwdv y fwd u == VPtr (Major (cp + (b - q))));
        assert (is_copy fwd cp)
      end
    | _ -> ()

/// The resolved target of a forwarded value: as before, or a copy.
let fv_target (#c: comps) (x: config c) (fwd: nat -> option nat) (m': mheap) (u: value) (a z: nat)
  : Lemma (requires fwd_to x fwd m' u /\ fwdv (vw x).yng fwd u == VPtr (Major a) /\ resolve m' a == Some z)
          (ensures (u == VPtr (Major a) /\ resolve (mj x) a == Some z) \/ is_copy fwd z)
  = ()

/// Roots satisfy `fwd_ok`, with reachable major targets.
let root_ok (#c: comps) (x: config c) (u: value)
  : Lemma (requires rinv x /\ L.memP u (vw x).roots)
          (ensures fwd_ok x u /\ (forall (a t: nat). u == VPtr (Major a) /\ resolve (mj x) a == Some t ==> reachable (vw x) t))
  = let w = vw x in
    res_root w u;
    match u with
    | VPtr (Major a) ->
      let t = Some?.v (resolve w.maj a) in reach_root w a t; n_kept_lt x t
    | VPtr (Young b) ->
      let q = Some?.v (resolve w.yng b) in
      let r : mlive w q = LRoot q b () in ()
    | _ -> ()

/// Fields of a block the program may use satisfy it when it is reachable or
/// live; their young pointers always forward.
let lt_young (#c: comps) (x: config c) (z j b: nat)
  : Lemma (requires rinv x /\ live_target c.a x.ph x.ast x.w.cmaj (mj x) z /\ ptr_field (mj x) z j /\
                    field (mj x) z j == VPtr (Young b))
          (ensures fwd_ok x (VPtr (Young b)))
  = let w = vw x in
    reveal_opaque (`%r_young) (r_young #c);
    let q = Some?.v (resolve w.yng b) in
    let r : mlive w q = LRem q z j b () in ()

let reach_field_ok (#c: comps) (x: config c) (z j: nat)
  : Lemma (requires rinv x /\ reachable (vw x) z /\ ptr_field (mj x) z j)
          (ensures fwd_ok x (field (mj x) z j) /\
                   (forall (a t: nat). field (mj x) z j == VPtr (Major a) /\ resolve (mj x) a == Some t ==> reachable (vw x) t))
  = let w = vw x in
    n_kept_lt x z;
    res_maj w z j;
    match field w.maj z j with
    | VPtr (Major a) -> let t = Some?.v (resolve w.maj a) in reach_field w z j a t; n_kept_lt x t
    | VPtr (Young b) -> lt_young x z j b
    | _ -> ()

let live_field_ok (#c: comps) (x: config c) (z j: nat)
  : Lemma (requires rinv x /\ Marking? x.ph /\ union x.snap x.allocd z /\ ptr_field (mj x) z j)
          (ensures fwd_ok x (field (mj x) z j) /\
                   (forall (a t: nat). field (mj x) z j == VPtr (Major a) /\ resolve (mj x) a == Some t ==> union x.snap x.allocd t))
  = n_live_lt x z;
    match field (mj x) z j with
    | VPtr (Major a) ->
      closed_step x z j a;
      eliminate exists (t: nat). resolve (mj x) a == Some t /\ union x.snap x.allocd t /\ in_use_c x t
      with n_live_lt x t
    | VPtr (Young b) -> lt_young x z j b
    | _ -> ()

/// Fields of a traced young object satisfy it, with reachable major targets.
let young_field_ok (#c: comps) (x: config c) (q j: nat)
  : Lemma (requires rinv x /\ minor_live (vw x) q /\ ptr_field (vw x).yng q j)
          (ensures fwd_ok x (field (vw x).yng q j) /\
                   (forall (a t: nat). field (vw x).yng q j == VPtr (Major a) /\ resolve (mj x) a == Some t ==> reachable (vw x) t))
  = let w = vw x in
    res_yng w q j;
    match field w.yng q j with
    | VPtr (Major a) -> let t = Some?.v (resolve w.maj a) in reach_young w q j a t; n_kept_lt x t
    | VPtr (Young b) ->
      let q' = Some?.v (resolve w.yng b) in
      let r0 = FStar.IndefiniteDescription.indefinite_description_ghost (mlive w q) (fun _ -> True) in
      let r : mlive w q' = LStep q q' r0 () in ()
    | _ -> ()

/// A copy's field is its young object's field, forwarded.
let copy_field (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap) (cp j: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ is_copy fwd cp /\ ptr_field m' cp j)
          (ensures exists (q: nat). fwd q == Some cp /\ minor_live (vw x) q /\ ptr_field (vw x).yng q j /\
                                    field m' cp j == fwdv (vw x).yng fwd (field (vw x).yng q j))
  = eliminate exists (q: nat). fwd q == Some cp
    with begin
      n_copy x x' hc' st' roots' fwd m' q cp;
      mp_copy x hc' st' roots' fwd m' q cp;
      mp_fwd x hc' st' roots' fwd m' q
    end

/// An old block's field the program may use, forwarded.
let old_field (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap) (z j: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ live_target c.a x.ph x.ast x.w.cmaj (mj x) z /\ ptr_field m' z j)
          (ensures ptr_field (mj x) z j /\ field m' z j == fwdv (vw x).yng fwd (field (mj x) z j))
  = n_keepsy x x' hc' st' roots' fwd m' z

/// ---------------------------------------------------------------------------
/// Reachability
/// ---------------------------------------------------------------------------

let s_cp (#c: comps) (x: config c) (fwd: nat -> option nat) (z: nat) : prop = reachable (vw x) z \/ is_copy fwd z

let n_root (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) (a z: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ L.memP (VPtr (Major a)) (wnext x fwd m').roots /\
                    resolve m' a == Some z)
          (ensures s_cp x fwd z)
  = LP.memP_map_elim (fwdv (vw x).yng fwd) (VPtr (Major a)) (vw x).roots;
    eliminate exists (u: value). L.memP u (vw x).roots /\ fwdv (vw x).yng fwd u == VPtr (Major a)
    with begin
      root_ok x u;
      fv x x' hc' st' roots' fwd m' u;
      fv_target x fwd m' u a z
    end

let n_outside (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap) (z: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ outside_ref (wnext x fwd m') z) (ensures s_cp x fwd z)
  = let w' = wnext x fwd m' in
    if FStar.IndefiniteDescription.strong_excluded_middle (root_ref w' z) then begin
      eliminate exists (a: nat). L.memP (VPtr (Major a)) w'.roots /\ resolve w'.maj a == Some z
      with n_root x x' hc' st' roots' fwd m' a z
    end else
      eliminate exists (y i a: nat). ptr_field w'.yng y i /\ field w'.yng y i == VPtr (Major a) /\
                                     resolve w'.maj a == Some z
      with ()

let n_edge (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) (y z: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ s_cp x fwd y /\ major_edge m' y z) (ensures s_cp x fwd z)
  = eliminate exists (j a: nat). ptr_field m' y j /\ field m' y j == VPtr (Major a) /\ resolve m' a == Some z
    with begin
      if FStar.IndefiniteDescription.strong_excluded_middle (reachable (vw x) y) then begin
        n_kept_lt x y;
        old_field x x' hc' st' roots' fwd m' y j;
        reach_field_ok x y j;
        fv x x' hc' st' roots' fwd m' (field (mj x) y j);
        fv_target x fwd m' (field (mj x) y j) a z
      end else begin
        copy_field x x' hc' st' roots' fwd m' y j;
        eliminate exists (q: nat). fwd q == Some y /\ minor_live (vw x) q /\ ptr_field (vw x).yng q j /\
                                   field m' y j == fwdv (vw x).yng fwd (field (vw x).yng q j)
        with begin
          young_field_ok x q j;
          fv x x' hc' st' roots' fwd m' (field (vw x).yng q j);
          fv_target x fwd m' (field (vw x).yng q j) a z
        end
      end
    end

let n_reach (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
    (m': mheap) (z: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ reachable (wnext x fwd m') z) (ensures s_cp x fwd z)
  = C.forall_intro (C.move_requires (n_outside x x' hc' st' roots' fwd m'));
    C.forall_intro_2 (fun y z -> C.move_requires (n_edge x x' hc' st' roots' fwd m' y) z);
    reachable_within (wnext x fwd m') (s_cp x fwd) z

let n_kept_new (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap) (z: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ s_cp x fwd z)
          (ensures kept_w x' (wnext x fwd m') z /\ (is_copy fwd z ==> ~(in_use_c x z)))
  = n_iu x x' hc' st' roots' fwd m' z;
    if FStar.IndefiniteDescription.strong_excluded_middle (reachable (vw x) z) then n_kept_lt x z
    else eliminate exists (q: nat). fwd q == Some z with n_copy x x' hc' st' roots' fwd m' q z

let n_r_reach (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap)
  : Lemma (requires mok x x' hc' st' roots' fwd m')
          (ensures r_reach x' (wnext x fwd m') /\ rback_w x (wnext x fwd m'))
  = C.forall_intro (C.move_requires (n_reach x x' hc' st' roots' fwd m'));
    C.forall_intro (C.move_requires (n_kept_new x x' hc' st' roots' fwd m'));
    reveal_opaque (`%r_reach) (r_reach #c);
    reveal_opaque (`%rback_w) (rback_w #c)

/// ---------------------------------------------------------------------------
/// Pointers after the step
/// ---------------------------------------------------------------------------

let fv_resolves (#c: comps) (x: config c) (fwd: nat -> option nat) (m': mheap) (u: value)
  : Lemma (requires fwd_to x fwd m' u)
          (ensures resolves (wnext x fwd m') (fwdv (vw x).yng fwd u) /\ not (is_young (fwdv (vw x).yng fwd u)))
  = let w' = wnext x fwd m' in
    assert (w'.maj == m');
    match fwdv (vw x).yng fwd u with
    | VPtr (Major a') -> eliminate exists (t: nat). resolve m' a' == Some t /\
                           ((u == VPtr (Major a') /\ resolve (mj x) a' == Some t) \/ is_copy fwd t)
                         with ()
    | _ -> ()

let n_res_root (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap) (v: value)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ L.memP v (wnext x fwd m').roots)
          (ensures resolves (wnext x fwd m') v)
  = LP.memP_map_elim (fwdv (vw x).yng fwd) v (vw x).roots;
    eliminate exists (u: value). L.memP u (vw x).roots /\ fwdv (vw x).yng fwd u == v
    with begin
      root_ok x u;
      fv x x' hc' st' roots' fwd m' u;
      fv_resolves x fwd m' u
    end

let n_res_maj (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap) (z j: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ reachable (wnext x fwd m') z /\ ptr_field m' z j)
          (ensures resolves (wnext x fwd m') (field m' z j))
  = n_reach x x' hc' st' roots' fwd m' z;
    if FStar.IndefiniteDescription.strong_excluded_middle (reachable (vw x) z) then begin
      n_kept_lt x z;
      old_field x x' hc' st' roots' fwd m' z j;
      reach_field_ok x z j;
      fv x x' hc' st' roots' fwd m' (field (mj x) z j);
      fv_resolves x fwd m' (field (mj x) z j)
    end else begin
      copy_field x x' hc' st' roots' fwd m' z j;
      eliminate exists (q: nat). fwd q == Some z /\ minor_live (vw x) q /\ ptr_field (vw x).yng q j /\
                                 field m' z j == fwdv (vw x).yng fwd (field (vw x).yng q j)
      with begin
        young_field_ok x q j;
        fv x x' hc' st' roots' fwd m' (field (vw x).yng q j);
        fv_resolves x fwd m' (field (vw x).yng q j)
      end
    end

let n_r_res (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap)
  : Lemma (requires mok x x' hc' st' roots' fwd m') (ensures r_res (wnext x fwd m'))
  = C.forall_intro (C.move_requires (n_res_root x x' hc' st' roots' fwd m'));
    C.forall_intro_2 (fun z j -> C.move_requires (n_res_maj x x' hc' st' roots' fwd m' z) j);
    reveal_opaque (`%r_res) r_res

/// No young pointer is left in a block the program may use.
let n_young1 (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap) (z j b: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ live_target c.a x'.ph x'.ast x'.w.cmaj m' z /\
                    ptr_field m' z j /\ field m' z j == VPtr (Young b))
          (ensures False)
  = n_iu x x' hc' st' roots' fwd m' z;
    if in_use_c x z then begin
      assert (live_target c.a x.ph x.ast x.w.cmaj (mj x) z);
      old_field x x' hc' st' roots' fwd m' z j;
      match field (mj x) z j with
      | VPtr (Young b0) -> lt_young x z j b0; fv x x' hc' st' roots' fwd m' (field (mj x) z j)
      | _ -> ()
    end else begin
      copy_field x x' hc' st' roots' fwd m' z j;
      eliminate exists (q: nat). fwd q == Some z /\ minor_live (vw x) q /\ ptr_field (vw x).yng q j /\
                                 field m' z j == fwdv (vw x).yng fwd (field (vw x).yng q j)
      with begin
        young_field_ok x q j;
        fv x x' hc' st' roots' fwd m' (field (vw x).yng q j)
      end
    end

let n_r_young (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap)
  : Lemma (requires mok x x' hc' st' roots' fwd m') (ensures r_young x' (wnext x fwd m'))
  = C.forall_intro_3 (fun z j b -> C.move_requires (n_young1 x x' hc' st' roots' fwd m' z j) b);
    reveal_opaque (`%r_young) (r_young #c)

let n_r_heap (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap)
  : Lemma (requires mok x x' hc' st' roots' fwd m') (ensures r_heap x' (wnext x fwd m'))
  = n_wf x x' hc' st' roots' fwd m';
    mp_basic x hc' st' roots' fwd m';
    canonical_empty (vw x).yng.size;
    reveal_opaque (`%r_heap) (r_heap #c)

/// ---------------------------------------------------------------------------
/// Colours
/// ---------------------------------------------------------------------------

let n_col1 (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap) (z: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ iu x' m' z)
          (ensures (in_use_c x z /\ col_of m' z == col_of (mj x) z /\ ~(is_copy fwd z)) \/
                   (is_copy fwd z /\ ~(in_use_c x z) /\ col_of m' z == colour_at c.k x.ph z))
  = n_iu x x' hc' st' roots' fwd m' z;
    if in_use_c x z then ()
    else eliminate exists (q: nat). fwd q == Some z with n_copy x x' hc' st' roots' fwd m' q z

let n_live (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap) (z: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ ~(Idle? x.ph) /\ live x' z)
          (ensures iu x' m' z /\ (~(is_copy fwd z) ==> live x z /\ in_use_c x z))
  = n_iu x x' hc' st' roots' fwd m' z;
    if FStar.IndefiniteDescription.strong_excluded_middle (live x z) then reveal_opaque (`%r_live) (r_live #c)

let n_col_sweep (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap) (p: c.k.progress) (z: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ x.ph == Sweeping p /\ iu x' m' z)
          (ensures col_sweep x' p m' z /\ (c.k.unswept p z == false ==> live x' z))
  = n_col1 x x' hc' st' roots' fwd m' z;
    if in_use_c x z then begin
      reveal_opaque (`%r_col) (r_col #c);
      reveal_opaque (`%r_live) (r_live #c);
      assert (col_sweep x p (mj x) z)
    end

let n_col_idle (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap) (z: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ Idle? x.ph /\ iu x' m' z)
          (ensures not (dark (col_of m' z)))
  = n_col1 x x' hc' st' roots' fwd m' z;
    if in_use_c x z then reveal_opaque (`%r_col) (r_col #c)

let n_tri (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ Marking? x.ph) (ensures tri_iu x' m' /\ scan_ok x' m')
  = let m = mj x in
    n_wf x x' hc' st' roots' fwd m';
    C.forall_intro (C.move_requires (n_live x x' hc' st' roots' fwd m'));
    let c2 (z: nat) : Lemma (iu x' m' z /\ dark (col_of m' z) ==> live x' z)
      = if iu x' m' z then begin
          n_col1 x x' hc' st' roots' fwd m' z;
          if in_use_c x z then reveal_opaque (`%r_col) (r_col #c)
        end in
    C.forall_intro c2;
    let c3 (z: nat) : Lemma (x'.allocd z ==> col_of m' z == Black)
      = if FStar.IndefiniteDescription.strong_excluded_middle (x'.allocd z) then begin
          n_live x x' hc' st' roots' fwd m' z;
          n_col1 x x' hc' st' roots' fwd m' z;
          if in_use_c x z then reveal_opaque (`%r_col) (r_col #c)
        end in
    C.forall_intro c3;
    let lv (y: nat) : Lemma (union x.snap x.allocd y ==> keepsy m m' y /\ union x'.snap x'.allocd y)
      = if FStar.IndefiniteDescription.strong_excluded_middle (union x.snap x.allocd y) then begin
          n_live_lt x y;
          n_keepsy x x' hc' st' roots' fwd m' y
        end in
    C.forall_intro lv;
    reveal_opaque (`%r_col) (r_col #c);
    scan_keepy x x' m m';
    let c4 (z: nat) : Lemma (x'.snap z /\ col_of m' z == White ==> live_reached m' (scan_of x') (union x'.snap x'.allocd) z)
      = if FStar.IndefiniteDescription.strong_excluded_middle (x'.snap z /\ col_of m' z == White) then begin
          n_live_lt x z;
          n_keepsy x x' hc' st' roots' fwd m' z;
          lpath_keepy m m' (scan_of x) (union x.snap x.allocd) (union x'.snap x'.allocd) z
        end in
    C.forall_intro c4

let n_closed1 (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap) (z j a: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ Marking? x.ph /\ union x'.snap x'.allocd z /\
                    ptr_field m' z j /\ field m' z j == VPtr (Major a))
          (ensures exists (t: nat). resolve m' a == Some t /\ union x'.snap x'.allocd t)
  = n_live x x' hc' st' roots' fwd m' z;
    if FStar.IndefiniteDescription.strong_excluded_middle (is_copy fwd z) then begin
      copy_field x x' hc' st' roots' fwd m' z j;
      eliminate exists (q: nat). fwd q == Some z /\ minor_live (vw x) q /\ ptr_field (vw x).yng q j /\
                                 field m' z j == fwdv (vw x).yng fwd (field (vw x).yng q j)
      with begin
        young_field_ok x q j;
        fv x x' hc' st' roots' fwd m' (field (vw x).yng q j);
        let t = Some?.v (resolve m' a) in
        fv_target x fwd m' (field (vw x).yng q j) a t;
        if FStar.IndefiniteDescription.strong_excluded_middle (reachable (vw x) t) then n_kept_lt x t
      end
    end else begin
      n_live_lt x z;
      old_field x x' hc' st' roots' fwd m' z j;
      live_field_ok x z j;
      fv x x' hc' st' roots' fwd m' (field (mj x) z j);
      let t = Some?.v (resolve m' a) in
      fv_target x fwd m' (field (mj x) z j) a t
    end

let n_r_col (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap)
  : Lemma (requires mok x x' hc' st' roots' fwd m')
          (ensures r_col x' (wnext x fwd m') /\ r_live x' (wnext x fwd m'))
  = reveal_opaque (`%r_col) (r_col #c);
    reveal_opaque (`%r_live) (r_live #c);
    match x.ph with
    | Idle -> C.forall_intro (C.move_requires (n_col_idle x x' hc' st' roots' fwd m'))
    | Marking ->
      n_tri x x' hc' st' roots' fwd m';
      C.forall_intro_3 (fun z j a -> C.move_requires (n_closed1 x x' hc' st' roots' fwd m' z j) a);
      C.forall_intro (C.move_requires (n_live x x' hc' st' roots' fwd m'))
    | Sweeping p ->
      C.forall_intro (C.move_requires (n_col_sweep x x' hc' st' roots' fwd m' p));
      C.forall_intro (C.move_requires (n_live x x' hc' st' roots' fwd m'))

/// ---------------------------------------------------------------------------
/// The conclusions
/// ---------------------------------------------------------------------------

let n_kept (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap) (z: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ c.n.collect x.ph x.ast x.w == Done hc' st' roots' fwd /\
                    kept x z)
          (ensures iu x' m' z == true /\ contents_w x EMinor (wnext x fwd m') z)
  = kept_live_target x (vw x) z;
    n_keepsy x x' hc' st' roots' fwd m' z

let n_word (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap) (n: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ n < (mj x).size /\ in_use_word_c x n)
          (ensures ~(free_w x' (wnext x fwd m') n))
  = n_wf x x' hc' st' roots' fwd m';
    eliminate exists (z: nat). covers (mj x) z n /\ in_use_c x z
    with begin
      n_iu x x' hc' st' roots' fwd m' z;
      in_use_not_free c.a x'.ast x'.w.cmaj m' z n
    end

let n_measure1 (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap) (z: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ Marking? x.ph)
          (ensures (white_live m' (live x') z ==> white_live (mj x) (live x') z) /\
                   (grey_live m' (live x') z ==> grey_live (mj x) (live x') z))
  = if FStar.IndefiniteDescription.strong_excluded_middle (live x' z) then begin
      n_live x x' hc' st' roots' fwd m' z;
      n_col1 x x' hc' st' roots' fwd m' z;
      n_wf x x' hc' st' roots' fwd m'
    end

let n_cs (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap)
  : Lemma (requires mok x x' hc' st' roots' fwd m' /\ c.n.collect x.ph x.ast x.w == Done hc' st' roots' fwd)
          (ensures (let w' = wnext x fwd m' in
                    cs_keep x EMinor x' w' /\ cs_alloc x EMinor x' w' /\ cs_words x EMinor x' w' /\
                    cs_mark x EMinor x' w' /\ cs_old x EMinor x'))
  = C.forall_intro (C.move_requires (n_kept x x' hc' st' roots' fwd m'));
    reveal_opaque (`%cs_keep) (cs_keep #c);
    reveal_opaque (`%cs_alloc) (cs_alloc #c);
    C.forall_intro (C.move_requires (n_word x x' hc' st' roots' fwd m'));
    reveal_opaque (`%cs_words) (cs_words #c);
    (if Marking? x.ph then begin
      C.forall_intro (C.move_requires (n_measure1 x x' hc' st' roots' fwd m'));
      n_wf x x' hc' st' roots' fwd m';
      reveal_opaque (`%r_col) (r_col #c);
      (match scan_of x with Some (s, _) -> (n_live_lt x s; n_keepsy x x' hc' st' roots' fwd m' s) | None -> ());
      fleft_keepy x (mj x) m'
    end);
    reveal_opaque (`%cs_mark) (cs_mark #c);
    C.forall_intro (mp_fwd x hc' st' roots' fwd m')

/// ---------------------------------------------------------------------------
/// EMinor
/// ---------------------------------------------------------------------------

let n_cyc1 (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap) (y: nat)
  : Lemma (requires mok x x' hc' st' roots' fwd m')
          (ensures (x'.allocd y ==> x.allocd y \/ in_use_c x y == false) /\
                   (iu x' m' y == true /\ in_use_c x y == false ==> x'.allocd y) /\
                   (in_use_c x y == true ==> iu x' m' y == true /\ wz_of m' y == wz_of (mj x) y))
  = n_iu x x' hc' st' roots' fwd m' y;
    if FStar.IndefiniteDescription.strong_excluded_middle (is_copy fwd y) then
      eliminate exists (q: nat). fwd q == Some y with n_copy x x' hc' st' roots' fwd m' q y;
    if in_use_c x y then n_wf x x' hc' st' roots' fwd m'

let n_cyc (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap)
  : Lemma (requires mok x x' hc' st' roots' fwd m') (ensures cs_cyc x x' (wnext x fwd m'))
  = C.forall_intro (n_cyc1 x x' hc' st' roots' fwd m');
    n_wf x x' hc' st' roots' fwd m';
    reveal_opaque (`%cs_cyc) (cs_cyc #c)

let n_finish (#c: comps) (x x': config c) (hc': c.t) (st': c.a.state) (roots': list value)
    (fwd: nat -> option nat) (m': mheap)
  : Lemma (requires faithful c.r /\ mok x x' hc' st' roots' fwd m' /\
                    c.n.collect x.ph x.ast x.w == Done hc' st' roots' fwd /\ views x' (wnext x fwd m'))
          (ensures rinv x' /\ concl_step x EMinor x' /\ rback x x' /\ cyc x x')
  = n_r_heap x x' hc' st' roots' fwd m';
    n_r_reach x x' hc' st' roots' fwd m';
    n_r_res x x' hc' st' roots' fwd m';
    n_r_young x x' hc' st' roots' fwd m';
    n_r_col x x' hc' st' roots' fwd m';
    n_cs x x' hc' st' roots' fwd m';
    n_cyc x x' hc' st' roots' fwd m';
    step_out_intro x EMinor x' (wnext x fwd m')

/// Out of room: the run stops, nothing else changes.
let oor_step (#c: comps) (x: config c)
  : Lemma (requires faithful c.r /\ rinv x /\ c.n.collect x.ph x.ast x.w == OutOfRoom)
          (ensures (let x' = step c x EMinor in rinv x' /\ concl_step x EMinor x' /\ rback x x' /\ cyc x x'))
  = let x' = step c x EMinor in
    let w = vw x in
    vw_views x;
    assert (views x' w);
    reveal_opaque (`%r_heap) (r_heap #c);
    reveal_opaque (`%r_reach) (r_reach #c);
    reveal_opaque (`%r_young) (r_young #c);
    reveal_opaque (`%r_col) (r_col #c);
    reveal_opaque (`%r_live) (r_live #c);
    assert (rinv_w x' w);
    reveal_opaque (`%cs_keep) (cs_keep #c);
    reveal_opaque (`%cs_alloc) (cs_alloc #c);
    agree_refl w.maj;
    same_words x EMinor x' w;
    same_mark x EMinor x' w;
    reveal_opaque (`%rback_w) (rback_w #c);
    cyc_agree x x' w;
    step_out_intro x EMinor x' w

/// The configuration after a collection that succeeds.
let minor_next (#c: comps) (x: config c) (hc': c.t) (st': c.a.state) (roots': list value) (fwd: nat -> option nat)
  : Lemma (requires c.n.collect x.ph x.ast x.w == Done hc' st' roots' fwd)
          (ensures (let x' = step c x EMinor in
                    x'.ph == x.ph /\ x'.ast == st' /\ x'.w.cmaj == hc' /\ x'.w.croots == roots' /\ x'.w.crem == [] /\
                    x'.w.cyng == c.r.yreset x.w.cyng /\ x'.snap == x.snap /\ x'.ms == x.ms /\
                    (forall (p: nat). x'.allocd p <==> x.allocd p \/ is_copy fwd p)))
  = ()

#push-options "--z3rlimit 40"
let minor_step (#c: comps) (x: config c)
  : Lemma (requires faithful c.r /\ rinv x /\ hyps_at c x EMinor)
          (ensures (let x' = step c x EMinor in rinv x' /\ concl_step x EMinor x' /\ rback x x' /\ cyc x x'))
  = let x' = step c x EMinor in
    let w = vw x in
    vw_views x;
    minor_pre_of x;
    assert (minor_m c.r c.n x.ph x.ast x.w w);
    match c.n.collect x.ph x.ast x.w with
    | OutOfRoom -> oor_step x
    | Done hc' st' roots' fwd ->
      let m' = FStar.IndefiniteDescription.indefinite_description_ghost mheap
                 (fun m' -> c.r.repr m' hc' /\ minor_post_done c.a x.ph x.ast x.w.cmaj w hc' st' roots' fwd m') in
      reveal_opaque (`%mpost) (mpost #c);
      assert (mpost x hc' st' roots' fwd m');
      assert (c.r.yrepr (empty_heap w.yng.size) (c.r.yreset x.w.cyng));
      minor_next x hc' st' roots' fwd;
      assert (mok x x' hc' st' roots' fwd m');
      assert (views x' (wnext x fwd m'));
      n_finish x x' hc' st' roots' fwd m'
#pop-options
