/// ---------------------------------------------------------------------------
/// GC.Spec.Top.StepMut - the mutator's steps that leave the major heap
/// ---------------------------------------------------------------------------
///
/// Design doc §16.6 (module 4): `ERead`, `ERoots`, `EYoungAlloc` and
/// `EWrite (Young _)`, and the read clause.  None of them changes the major
/// heap, the allocator or the remembered set; each changes the roots or the
/// nursery.  `mut_step` is the common argument: if the new nursery keeps
/// every young pointer resolving, every new root or young field resolves, and
/// every new outside ref was reachable, then the invariant holds again,
/// nothing new is reachable, and `concl_step` holds.

module GC.Spec.Top.StepMut

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Views
open GC.Spec.Top.Words
open GC.Spec.Top.RInv
open GC.Spec.Top.StepBase
module L = FStar.List.Tot
module C = FStar.Classical

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The common argument
/// ---------------------------------------------------------------------------

let same_cfg (#c: comps) (x x': config c) : prop =
  x'.ph == x.ph /\ x'.ast == x.ast /\ x'.w.cmaj == x.w.cmaj /\ x'.snap == x.snap /\ x'.allocd == x.allocd /\ x'.ms == x.ms

let yres_kept (y y': mheap) : prop = forall (b o: nat). resolve y b == Some o ==> resolve y' b == Some o

/// What a mutator step must show of its new world.
let mut_ok (#c: comps) (x x': config c) (w': world) : prop =
  let w = vw x in
  views x' w' /\ w'.maj == w.maj /\ w'.rem == w.rem /\ same_cfg x x' /\
  young_ok w'.yng /\ yres_kept w.yng w'.yng /\
  (forall (o i: nat). ptr_field w'.yng o i ==> resolves w' (field w'.yng o i)) /\
  (forall (v: value). L.memP v w'.roots ==> resolves w' v) /\
  (forall (o: nat). outside_ref w' o ==> reachable w o)

let mut_reach (#c: comps) (x x': config c) (w': world) (o: nat)
  : Lemma (requires mut_ok x x' w' /\ reachable w' o) (ensures reachable (vw x) o)
  = let w = vw x in
    C.forall_intro_2 (fun (a b: nat) -> C.move_requires (reach_edge w a) b);
    reachable_within w' (reachable w) o

let resolves_kept (w w': world) (v: value)
  : Lemma (requires w'.maj == w.maj /\ yres_kept w.yng w'.yng /\ resolves w v) (ensures resolves w' v)
  = match v with
    | VPtr (Young b) -> let o = Some?.v (resolve w.yng b) in assert (resolve w'.yng b == Some o)
    | _ -> ()

let mut_r_reach (#c: comps) (x x': config c) (w': world)
  : Lemma (requires rinv x /\ mut_ok x x' w') (ensures r_reach x' w' /\ rback_w x w')
  = C.forall_intro (C.move_requires (mut_reach x x' w'));
    C.forall_intro (C.move_requires (reach_kept x (vw x)));
    reveal_opaque (`%r_reach) (r_reach #c);
    reveal_opaque (`%rback_w) (rback_w #c)

let mut_res1 (#c: comps) (x x': config c) (w': world) (o i: nat)
  : Lemma (requires rinv x /\ mut_ok x x' w' /\ reachable w' o /\ ptr_field w'.maj o i)
          (ensures resolves w' (field w'.maj o i))
  = mut_reach x x' w' o;
    res_maj (vw x) o i;
    resolves_kept (vw x) w' (field (vw x).maj o i)

let mut_r_res (#c: comps) (x x': config c) (w': world)
  : Lemma (requires rinv x /\ mut_ok x x' w') (ensures r_res w')
  = C.forall_intro_2 (fun o i -> C.move_requires (mut_res1 x x' w' o) i);
    reveal_opaque (`%r_res) r_res

let mut_young1 (#c: comps) (x x': config c) (w': world) (o i b: nat)
  : Lemma (requires rinv x /\ mut_ok x x' w' /\ live_target c.a x'.ph x'.ast x'.w.cmaj w'.maj o /\
                    ptr_field w'.maj o i /\ field w'.maj o i == VPtr (Young b))
          (ensures Some? (resolve w'.yng b) /\ L.memP (o, i) w'.rem)
  = reveal_opaque (`%r_young) (r_young #c);
    let w = vw x in
    assert (Some? (resolve w.yng b));
    let y = Some?.v (resolve w.yng b) in
    assert (resolve w'.yng b == Some y)

let mut_r_young (#c: comps) (x x': config c) (w': world)
  : Lemma (requires rinv x /\ mut_ok x x' w') (ensures r_young x' w')
  = C.forall_intro_3 (fun o i b -> C.move_requires (mut_young1 x x' w' o i) b);
    reveal_opaque (`%r_young) (r_young #c)

let mut_r_rest (#c: comps) (x x': config c) (w': world)
  : Lemma (requires rinv x /\ mut_ok x x' w') (ensures r_heap x' w' /\ r_col x' w' /\ r_live x' w')
  = reveal_opaque (`%r_heap) (r_heap #c);
    reveal_opaque (`%r_col) (r_col #c);
    reveal_opaque (`%r_live) (r_live #c)

/// **A mutator step that leaves the major heap.**
let mut_step (#c: comps) (x: config c) (e: event) (x': config c) (w': world)
  : Lemma (requires faithful c.r /\ rinv x /\ mut_ok x x' w' /\ cs_old x e x' /\
                    (ERead? e \/ ERoots? e \/ EYoungAlloc? e \/ (EWrite? e /\ Young? (EWrite?.p e))))
          (ensures rinv x' /\ concl_step x e x' /\ rback x x' /\ cyc x x')
  = mut_r_reach x x' w'; mut_r_res x x' w'; mut_r_young x x' w'; mut_r_rest x x' w';
    reveal_opaque (`%r_heap) (r_heap #c);
    agree_refl (mj x);
    same_cs x e x' w';
    cyc_agree x x' w';
    step_out_intro x e x' w'

/// ---------------------------------------------------------------------------
/// The events
/// ---------------------------------------------------------------------------

let value_resolves (w: world) (v: value)
  : Lemma (requires value_ok w v) (ensures resolves w v)
  = ()

/// A new root that is a value the program may hold.
let root_reach_ok (w: world) (v: value) (o: nat)
  : Lemma (requires value_ok w v /\ (match v with VPtr (Major a) -> resolve w.maj a == Some o | _ -> False))
          (ensures reachable w o)
  = ()

/// The roots after a step that pushes `v`, or replaces them by `rs`, in a
/// world with the same major heap.
let roots_outside (w w': world) (o: nat)
  : Lemma (requires w'.maj == w.maj /\ root_ref w' o /\
                    (forall (v: value). L.memP v w'.roots ==> L.memP v w.roots \/
                       (match v with VPtr (Major a) -> (forall (o': nat). resolve w.maj a == Some o' ==> reachable w o')
                                   | _ -> True)))
          (ensures reachable w o)
  = let a = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun a -> L.memP (VPtr (Major a)) w'.roots /\ resolve w'.maj a == Some o) in
    if FStar.IndefiniteDescription.strong_excluded_middle (L.memP (VPtr (Major a)) w.roots) then reach_root w a o

/// Young refs of a nursery whose pointer fields are the old ones, or values
/// whose targets are reachable.
let yref_cond (w w': world) : prop =
  forall (y i a: nat). ptr_field w'.yng y i /\ field w'.yng y i == VPtr (Major a) ==>
    (ptr_field w.yng y i /\ field w.yng y i == VPtr (Major a)) \/
    (forall (o': nat). resolve w.maj a == Some o' ==> reachable w o')

let yref_outside1 (w w': world) (o y i a: nat)
  : Lemma (requires w'.maj == w.maj /\ yref_cond w w' /\
                    ptr_field w'.yng y i /\ field w'.yng y i == VPtr (Major a) /\ resolve w'.maj a == Some o)
          (ensures reachable w o)
  = if FStar.IndefiniteDescription.strong_excluded_middle (ptr_field w.yng y i /\ field w.yng y i == VPtr (Major a))
    then reach_young w y i a o

let yref_outside (w w': world) (o: nat)
  : Lemma (requires w'.maj == w.maj /\ young_ref w' o /\ yref_cond w w') (ensures reachable w o)
  = C.forall_intro_3 (fun y i a -> C.move_requires (yref_outside1 w w' o y i) a)

/// The read of field `i` of a major block is the model's.
let read_major (#c: comps) (x: config c) (o i: nat)
  : Lemma (requires faithful c.r /\ has_view x /\ ptr_field (mj x) o i)
          (ensures c.r.read x.w.cmaj o i == field (mj x) o i)
  = vw_views x

let read_young (#c: comps) (x: config c) (o i: nat)
  : Lemma (requires faithful c.r /\ has_view x /\ ptr_field (wv x).yng o i)
          (ensures c.r.yread x.w.cyng o i == field (wv x).yng o i)
  = vw_views x

/// ---------------------------------------------------------------------------
/// ERead
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let read_major_step (#c: comps) (x: config c) (o i: nat)
  : Lemma (requires faithful c.r /\ rinv x /\ mutator_ok x (ERead (Major o) i))
          (ensures (let x' = step c x (ERead (Major o) i) in rinv x' /\ concl_step x (ERead (Major o) i) x' /\ rback x x' /\ cyc x x'))
  = let e = ERead (Major o) i in
    let x' = step c x e in
    let w = vw x in
    let v = field w.maj o i in
    read_major x o i;
    let w' = { w with roots = v :: w.roots } in
    assert (views x' w');
    res_maj w o i;
    let out (o': nat) : Lemma (requires outside_ref w' o') (ensures reachable w o')
      = (match v with
         | VPtr (Major a) ->
           C.forall_intro (C.move_requires (reach_field w o i a))
         | _ -> ());
        C.move_requires (roots_outside w w') o';
        if FStar.IndefiniteDescription.strong_excluded_middle (young_ref w' o') then begin
          assert (young_ref w o'); reach_outside w o'
        end in
    C.forall_intro (C.move_requires out);
    C.forall_intro (C.move_requires (res_root w));
    C.forall_intro_2 (fun (a b: nat) -> C.move_requires (res_yng w a) b);
    reveal_opaque (`%r_heap) (r_heap #c);
    assert (young_ok w'.yng /\ yres_kept w.yng w'.yng /\ same_cfg x x');
    assert (forall (v: value). L.memP v w'.roots ==> resolves w' v);
    assert (forall (o i: nat). ptr_field w'.yng o i ==> resolves w' (field w'.yng o i));
    assert (cs_old x e x');
    mut_step x e x' w'

let read_young_step (#c: comps) (x: config c) (o i: nat)
  : Lemma (requires faithful c.r /\ rinv x /\ mutator_ok x (ERead (Young o) i))
          (ensures (let x' = step c x (ERead (Young o) i) in rinv x' /\ concl_step x (ERead (Young o) i) x' /\ rback x x' /\ cyc x x'))
  = let e = ERead (Young o) i in
    let x' = step c x e in
    let w = vw x in
    let v = field w.yng o i in
    read_young x o i;
    let w' = { w with roots = v :: w.roots } in
    assert (views x' w');
    res_yng w o i;
    let out (o': nat) : Lemma (requires outside_ref w' o') (ensures reachable w o')
      = (match v with
         | VPtr (Major a) ->
           C.forall_intro (C.move_requires (reach_young w o i a))
         | _ -> ());
        C.move_requires (roots_outside w w') o';
        if FStar.IndefiniteDescription.strong_excluded_middle (young_ref w' o') then begin
          assert (young_ref w o'); reach_outside w o'
        end in
    C.forall_intro (C.move_requires out);
    C.forall_intro (C.move_requires (res_root w));
    C.forall_intro_2 (fun (a b: nat) -> C.move_requires (res_yng w a) b);
    reveal_opaque (`%r_heap) (r_heap #c);
    assert (young_ok w'.yng /\ yres_kept w.yng w'.yng /\ same_cfg x x');
    assert (forall (v: value). L.memP v w'.roots ==> resolves w' v);
    assert (forall (o i: nat). ptr_field w'.yng o i ==> resolves w' (field w'.yng o i));
    assert (cs_old x e x');
    mut_step x e x' w'

/// ---------------------------------------------------------------------------
/// ERoots
/// ---------------------------------------------------------------------------

let roots_step (#c: comps) (x: config c) (rs: list value)
  : Lemma (requires faithful c.r /\ rinv x /\ mutator_ok x (ERoots rs))
          (ensures (let x' = step c x (ERoots rs) in rinv x' /\ concl_step x (ERoots rs) x' /\ rback x x' /\ cyc x x'))
  = let e = ERoots rs in
    let x' = step c x e in
    let w = vw x in
    let w' = { w with roots = rs } in
    assert (views x' w');
    let out (o': nat) : Lemma (requires outside_ref w' o') (ensures reachable w o')
      = C.move_requires (roots_outside w w') o';
        if FStar.IndefiniteDescription.strong_excluded_middle (young_ref w' o') then begin
          assert (young_ref w o'); reach_outside w o'
        end in
    C.forall_intro (C.move_requires out);
    C.forall_intro_2 (fun (a b: nat) -> C.move_requires (res_yng w a) b);
    reveal_opaque (`%r_heap) (r_heap #c);
    assert (young_ok w'.yng /\ yres_kept w.yng w'.yng /\ same_cfg x x');
    assert (forall (v: value). L.memP v w'.roots ==> resolves w' v);
    assert (forall (o i: nat). ptr_field w'.yng o i ==> resolves w' (field w'.yng o i));
    assert (cs_old x e x');
    mut_step x e x' w'
#pop-options

/// ---------------------------------------------------------------------------
/// EYoungAlloc
/// ---------------------------------------------------------------------------

let yalloc_fields (w w': world) (n: nat) (sz: size_t) (tag: tag_t) (vs: list value) (o i: nat)
  : Lemma (requires r_res w /\ young_ok w.yng /\ young_free w.yng n sz /\ L.length vs == sz /\
                    tag <> infix_tag /\ fill_ok w tag vs /\
                    w'.maj == w.maj /\ w'.yng == young_alloc w.yng n sz tag vs /\ ptr_field w'.yng o i)
          (ensures resolves w' (field w'.yng o i) /\
                   (forall (a: nat). field w'.yng o i == VPtr (Major a) ==>
                      (ptr_field w.yng o i /\ field w.yng o i == VPtr (Major a)) \/
                      (forall (o': nat). resolve w.maj a == Some o' ==> reachable w o')))
  = C.forall_intro_2 (fun b y -> C.move_requires (yalloc_resolve w.yng n sz tag vs b) y);
    if o = n then begin
      assert (n < w.yng.size);
      assert (wz_of w'.yng n == sz /\ tag_of w'.yng n == tag);
      assert (i < sz /\ scannable tag);
      yalloc_new_field w.yng n sz tag vs i;
      let v = L.index vs i in
      assert (value_ok w v);
      value_resolves w v;
      resolves_kept w w' v;
      assert (field w'.yng o i == v)
    end else begin
      assert ((young_alloc w.yng n sz tag vs).hd o == w.yng.hd o);
      assert (is_block w.yng o);
      yalloc_keeps w.yng n sz tag vs o;
      assert (ptr_field w.yng o i /\ field w'.yng o i == field w.yng o i);
      res_yng w o i;
      resolves_kept w w' (field w.yng o i)
    end

#push-options "--z3rlimit 40"
let yalloc_step (#c: comps) (x: config c) (sz: size_t) (tag: tag_t) (vs: list value)
  : Lemma (requires faithful c.r /\ rinv x /\ mutator_ok x (EYoungAlloc sz tag vs) /\
                    hyps_at c x (EYoungAlloc sz tag vs) /\ enabled c x (EYoungAlloc sz tag vs))
          (ensures (let e = EYoungAlloc sz tag vs in
                    let x' = step c x e in rinv x' /\ concl_step x e x' /\ rback x x' /\ cyc x x'))
  = let e = EYoungAlloc sz tag vs in
    let x' = step c x e in
    let w = vw x in
    vw_views x;
    reveal_opaque (`%r_heap) (r_heap #c);
    let Some (n, y2) = c.r.yalloc x.w.cyng sz tag vs in
    assert (young_free w.yng n sz /\ c.r.yrepr (young_alloc w.yng n sz tag vs) y2);
    let w' = { w with yng = young_alloc w.yng n sz tag vs; roots = VPtr (Young n) :: w.roots } in
    assert (views x' w');
    yalloc_young_ok w.yng n sz tag vs;
    C.forall_intro_2 (fun b y -> C.move_requires (yalloc_resolve w.yng n sz tag vs b) y);
    C.forall_intro_2 (fun o i -> C.move_requires (yalloc_fields w w' n sz tag vs o) i);
    yalloc_new_field w.yng n sz tag vs 0;
    let rt (v: value) : Lemma (requires L.memP v w'.roots) (ensures resolves w' v)
      = if v = VPtr (Young n) then () else begin res_root w v; resolves_kept w w' v end in
    C.forall_intro (C.move_requires rt);
    let out (o': nat) : Lemma (requires outside_ref w' o') (ensures reachable w o')
      = C.move_requires (roots_outside w w') o';
        C.move_requires (yref_outside w w') o' in
    C.forall_intro (C.move_requires out);
    mut_step x e x' w'
#pop-options

/// ---------------------------------------------------------------------------
/// EWrite (Young _)
/// ---------------------------------------------------------------------------

let ywrite_fields (w w': world) (o i: nat) (v: value) (y j: nat)
  : Lemma (requires r_res w /\ young_ok w.yng /\ is_block w.yng o /\ i < wz_of w.yng o /\
                    tag_of w.yng o <> closure_tag /\ (scannable (tag_of w.yng o) ==> value_ok w v) /\
                    w'.maj == w.maj /\ w'.yng == set_field w.yng o i v /\ ptr_field w'.yng y j)
          (ensures resolves w' (field w'.yng y j) /\
                   (forall (a: nat). field w'.yng y j == VPtr (Major a) ==>
                      (ptr_field w.yng y j /\ field w.yng y j == VPtr (Major a)) \/
                      (forall (o': nat). resolve w.maj a == Some o' ==> reachable w o')))
  = C.forall_intro (set_field_resolve w.yng o i v);
    if y = o && j = i then ()
    else begin
      set_field_other w.yng o i y j v;
      res_yng w y j;
      resolves_kept w w' (field w.yng y j)
    end

#push-options "--z3rlimit 40"
let ywrite_step (#c: comps) (x: config c) (o i: nat) (v: value)
  : Lemma (requires faithful c.r /\ rinv x /\ mutator_ok x (EWrite (Young o) i v) /\
                    hyps_at c x (EWrite (Young o) i v))
          (ensures (let e = EWrite (Young o) i v in
                    let x' = step c x e in rinv x' /\ concl_step x e x' /\ rback x x' /\ cyc x x'))
  = let e = EWrite (Young o) i v in
    let x' = step c x e in
    let w = vw x in
    vw_views x;
    reveal_opaque (`%r_heap) (r_heap #c);
    assert (c.r.yrepr (set_field w.yng o i v) (c.r.ywrite x.w.cyng o i v));
    let w' = { w with yng = set_field w.yng o i v } in
    assert (views x' w');
    set_field_young_ok w.yng o i v;
    C.forall_intro (set_field_resolve w.yng o i v);
    C.forall_intro_2 (fun y j -> C.move_requires (ywrite_fields w w' o i v y) j);
    let out (o': nat) : Lemma (requires outside_ref w' o') (ensures reachable w o')
      = if FStar.IndefiniteDescription.strong_excluded_middle (root_ref w' o') then begin
          assert (root_ref w o'); reach_outside w o'
        end;
        C.move_requires (yref_outside w w') o' in
    C.forall_intro (C.move_requires out);
    assert (yres_kept w.yng w'.yng);
    assert (same_cfg x x');
    assert (forall (o i: nat). ptr_field w'.yng o i ==> resolves w' (field w'.yng o i));
    let rt (u: value) : Lemma (requires L.memP u w'.roots) (ensures resolves w' u)
      = res_root w u; resolves_kept w w' u in
    C.forall_intro (C.move_requires rt);
    assert (cs_old x e x');
    mut_step x e x' w'
#pop-options
