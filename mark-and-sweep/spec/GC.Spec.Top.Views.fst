/// ---------------------------------------------------------------------------
/// GC.Spec.Top.Views - every model world of a configuration reads the same
/// ---------------------------------------------------------------------------
///
/// Design doc §16.1, §16.6 (module 1).  The conclusions read `vw x`, a world
/// chosen among those that represent the configuration, and each contract
/// hands back *some* model of the new heap.  Two model heaps representing one
/// concrete heap agree (`Rep.repr_agree`: same size, blocks, headers and
/// fields), so the choice does not matter once every predicate involved is
/// invariant under `agree`.  This module proves that for the predicates of
/// the run invariant and the conclusions:
///   - heaps: blocks, headers, fields, `covers`, `resolve`, `ptr_field`,
///     edges, `well_formed`, `young_ok`, the allocator's in-use and free
///     words, `live_target`, `sound_value`;
///   - worlds (`wagree`): `reachable`, `yreachable`, `minor_live`;
///   - colours: `wpath`, `tricolour`, `closed`, `white_live`, `grey_live`
///     and the mark's measures;
///   - configurations: any world that views `x` agrees with `vw x`.

module GC.Spec.Top.Views

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
module L = FStar.List.Tot
module C = FStar.Classical

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Heaps
/// ---------------------------------------------------------------------------

let ag_hd (m m': mheap) (o: nat)
  : Lemma (requires agree m m')
          (ensures is_block m o == is_block m' o /\
                   (is_block m o ==> m.hd o == m'.hd o /\ hdr_of m o == hdr_of m' o /\
                                     wz_of m o == wz_of m' o /\ tag_of m o == tag_of m' o /\
                                     col_of m o == col_of m' o))
  = ()

let ag_field (m m': mheap) (o i: nat)
  : Lemma (requires agree m m' /\ is_block m o /\ i < wz_of m o) (ensures field m o i == field m' o i)
  = assert (covers m' o (o + 1 + i))

/// A word covered by a block, past its header.
let ag_body (m m': mheap) (o w: nat)
  : Lemma (requires agree m m' /\ covers m o w /\ o < w) (ensures m.body w == m'.body w)
  = assert (covers m' o w)

let ag_resolve1 (m m': mheap) (a x: nat)
  : Lemma (requires agree m m' /\ resolve m a == Some x) (ensures resolve m' a == Some x)
  = if is_block m a then () else ag_body m m' x a

let ag_resolve (m m': mheap) (a: nat)
  : Lemma (requires agree m m') (ensures resolve m a == resolve m' a)
  = agree_sym m m';
    match resolve m a with
    | Some x -> ag_resolve1 m m' a x
    | None -> (match resolve m' a with Some x -> ag_resolve1 m' m a x | None -> ())

let ag_ptr_field (m m': mheap) (o i: nat)
  : Lemma (requires agree m m') (ensures ptr_field m o i == ptr_field m' o i)
  = ag_hd m m' o

let ag_covers (m m': mheap) (o w: nat)
  : Lemma (requires agree m m') (ensures covers m o w == covers m' o w)
  = agree_covers m m' o w

let ag_edge1 (m m': mheap) (o o' i a: nat)
  : Lemma (requires agree m m' /\ ptr_field m o i /\ field m o i == VPtr (Major a) /\ resolve m a == Some o')
          (ensures major_edge m' o o')
  = ag_hd m m' o; ag_field m m' o i; ag_resolve m m' a

let ag_edge (m m': mheap) (o o': nat)
  : Lemma (requires agree m m') (ensures major_edge m o o' ==> major_edge m' o o')
  = C.forall_intro_2 (fun i a -> C.move_requires (ag_edge1 m m' o o' i) a)

let ag_yedge1 (m m': mheap) (o o' i a: nat)
  : Lemma (requires agree m m' /\ ptr_field m o i /\ field m o i == VPtr (Young a) /\ resolve m a == Some o')
          (ensures young_edge m' o o')
  = ag_hd m m' o; ag_field m m' o i; ag_resolve m m' a

let ag_yedge (m m': mheap) (o o': nat)
  : Lemma (requires agree m m') (ensures young_edge m o o' ==> young_edge m' o o')
  = C.forall_intro_2 (fun i a -> C.move_requires (ag_yedge1 m m' o o' i) a)

let ag_tiled (m m': mheap)
  : Lemma (requires agree m m' /\ tiled m) (ensures tiled m')
  = C.forall_intro (fun (o: nat) -> ag_hd m m' o);
    C.forall_intro_2 (fun (o w: nat) -> ag_covers m m' o w)

let ag_well_formed (m m': mheap)
  : Lemma (requires agree m m' /\ well_formed m) (ensures well_formed m')
  = ag_tiled m m';
    C.forall_intro (fun (o: nat) -> ag_hd m m' o)

let ag_young_ok (m m': mheap)
  : Lemma (requires agree m m' /\ young_ok m) (ensures young_ok m')
  = C.forall_intro (fun (o: nat) -> ag_hd m m' o);
    C.forall_intro_2 (fun (o w: nat) -> ag_covers m m' o w)

/// The allocator's view: in use, free and in-use words, the blocks the
/// program may use, the values it may store.
let ag_in_use (#t: Type0) (#k: sweep_kind) (a: allocator t k) (st: a.state) (h: t) (m m': mheap) (o: nat)
  : Lemma (requires agree m m') (ensures in_use a st h m o == in_use a st h m' o)
  = ag_hd m m' o

let ag_free_word (#t: Type0) (#k: sweep_kind) (a: allocator t k) (st: a.state) (h: t) (m m': mheap) (w: nat)
  : Lemma (requires agree m m') (ensures free_word a st h m w <==> free_word a st h m' w)
  = C.forall_intro (fun (o: nat) -> ag_covers m m' o w)

let ag_in_use_word (#t: Type0) (#k: sweep_kind) (a: allocator t k) (st: a.state) (h: t) (m m': mheap) (w: nat)
  : Lemma (requires agree m m') (ensures in_use_word a st h m w <==> in_use_word a st h m' w)
  = C.forall_intro (fun (o: nat) -> ag_covers m m' o w; ag_in_use a st h m m' o)

let ag_live_target (#t: Type0) (#k: sweep_kind) (a: allocator t k) (ph: phase k.progress) (st: a.state)
    (h: t) (m m': mheap) (o: nat)
  : Lemma (requires agree m m') (ensures live_target a ph st h m o <==> live_target a ph st h m' o)
  = ag_hd m m' o

let ag_sound_value (#t: Type0) (#k: sweep_kind) (a: allocator t k) (ph: phase k.progress) (st: a.state)
    (h: t) (m m': mheap) (v: value)
  : Lemma (requires agree m m') (ensures sound_value a ph st h m v <==> sound_value a ph st h m' v)
  = match v with
    | VPtr (Major b) ->
      ag_resolve m m' b;
      C.forall_intro (C.move_requires (ag_live_target a ph st h m m'))
    | _ -> ()

/// ---------------------------------------------------------------------------
/// Worlds
/// ---------------------------------------------------------------------------

let wagree (w w': world) : prop =
  agree w.maj w'.maj /\ agree w.yng w'.yng /\ w.roots == w'.roots /\ w.rem == w'.rem

let wagree_refl (w: world) : Lemma (wagree w w) = ()

let wagree_sym (w w': world) : Lemma (requires wagree w w') (ensures wagree w' w)
  = agree_sym w.maj w'.maj; agree_sym w.yng w'.yng

let wagree_trans (w1 w2 w3: world)
  : Lemma (requires wagree w1 w2 /\ wagree w2 w3) (ensures wagree w1 w3)
  = agree_trans w1.maj w2.maj w3.maj; agree_trans w1.yng w2.yng w3.yng

let ag_root_ref (w w': world) (o a: nat)
  : Lemma (requires wagree w w' /\ L.memP (VPtr (Major a)) w.roots /\ resolve w.maj a == Some o)
          (ensures root_ref w' o)
  = ag_resolve w.maj w'.maj a

let ag_young_ref (w w': world) (o y i a: nat)
  : Lemma (requires wagree w w' /\ ptr_field w.yng y i /\ field w.yng y i == VPtr (Major a) /\
                    resolve w.maj a == Some o)
          (ensures young_ref w' o)
  = ag_resolve w.maj w'.maj a; ag_hd w.yng w'.yng y; ag_field w.yng w'.yng y i;
    assert (ptr_field w'.yng y i /\ field w'.yng y i == VPtr (Major a) /\ resolve w'.maj a == Some o)

let ag_outside (w w': world) (o: nat)
  : Lemma (requires wagree w w') (ensures outside_ref w o ==> outside_ref w' o)
  = C.forall_intro (C.move_requires (ag_root_ref w w' o));
    C.forall_intro_3 (fun y i a -> C.move_requires (ag_young_ref w w' o y i) a)

let rec ag_reach (w w': world) (o: nat) (r: reach w o)
  : Lemma (requires wagree w w') (ensures reachable w' o) (decreases r)
  = match r with
    | RBase _ _ ->
      ag_outside w w' o;
      let r' : reach w' o = RBase o () in ()
    | RStep x _ r0 _ ->
      ag_reach w w' x r0;
      ag_edge w.maj w'.maj x o;
      let r0' = FStar.IndefiniteDescription.indefinite_description_ghost (reach w' x) (fun _ -> True) in
      let r' : reach w' o = RStep x o r0' () in ()

let ag_reachable (w w': world) (o: nat)
  : Lemma (requires wagree w w') (ensures reachable w o <==> reachable w' o)
  = wagree_sym w w';
    let f (r: reach w o) : Lemma (reachable w' o) = ag_reach w w' o r in
    let g (r: reach w' o) : Lemma (reachable w o) = ag_reach w' w o r in
    C.forall_intro f;
    C.forall_intro g

let rec ag_yreach (w w': world) (o: nat) (r: yreach w o)
  : Lemma (requires wagree w w') (ensures yreachable w' o) (decreases r)
  = match r with
    | YRoot _ a _ ->
      ag_resolve w.yng w'.yng a;
      let r' : yreach w' o = YRoot o a () in ()
    | YOld _ x i a r0 _ ->
      ag_reach w w' x r0;
      ag_resolve w.yng w'.yng a;
      ag_hd w.maj w'.maj x; ag_field w.maj w'.maj x i;
      let r0' = FStar.IndefiniteDescription.indefinite_description_ghost (reach w' x) (fun _ -> True) in
      let r' : yreach w' o = YOld o x i a r0' () in ()
    | YStep x _ r0 _ ->
      ag_yreach w w' x r0;
      ag_yedge w.yng w'.yng x o;
      let r0' = FStar.IndefiniteDescription.indefinite_description_ghost (yreach w' x) (fun _ -> True) in
      let r' : yreach w' o = YStep x o r0' () in ()

let ag_yreachable (w w': world) (o: nat)
  : Lemma (requires wagree w w') (ensures yreachable w o <==> yreachable w' o)
  = wagree_sym w w';
    let f (r: yreach w o) : Lemma (yreachable w' o) = ag_yreach w w' o r in
    let g (r: yreach w' o) : Lemma (yreachable w o) = ag_yreach w' w o r in
    C.forall_intro f;
    C.forall_intro g

let rec ag_mlive (w w': world) (o: nat) (r: mlive w o)
  : Lemma (requires wagree w w') (ensures minor_live w' o) (decreases r)
  = match r with
    | LRoot _ a _ ->
      ag_resolve w.yng w'.yng a;
      let r' : mlive w' o = LRoot o a () in ()
    | LRem _ x i a _ ->
      ag_resolve w.yng w'.yng a;
      ag_hd w.maj w'.maj x; ag_field w.maj w'.maj x i;
      let r' : mlive w' o = LRem o x i a () in ()
    | LStep x _ r0 _ ->
      ag_mlive w w' x r0;
      ag_yedge w.yng w'.yng x o;
      let r0' = FStar.IndefiniteDescription.indefinite_description_ghost (mlive w' x) (fun _ -> True) in
      let r' : mlive w' o = LStep x o r0' () in ()

let ag_minor_live (w w': world) (o: nat)
  : Lemma (requires wagree w w') (ensures minor_live w o <==> minor_live w' o)
  = wagree_sym w w';
    let f (r: mlive w o) : Lemma (minor_live w' o) = ag_mlive w w' o r in
    let g (r: mlive w' o) : Lemma (minor_live w o) = ag_mlive w' w o r in
    C.forall_intro f;
    C.forall_intro g

let ag_value_ok (w w': world) (v: value)
  : Lemma (requires wagree w w') (ensures value_ok w v <==> value_ok w' v)
  = match v with
    | VPtr (Major a) ->
      ag_resolve w.maj w'.maj a;
      C.forall_intro (C.move_requires (ag_reachable w w'))
    | VPtr (Young a) ->
      ag_resolve w.yng w'.yng a;
      C.forall_intro (C.move_requires (ag_yreachable w w'))
    | _ -> ()

/// ---------------------------------------------------------------------------
/// Colours
/// ---------------------------------------------------------------------------

let rec ag_wpath (m m': mheap) (o: nat) (p: wpath m o)
  : Lemma (requires agree m m') (ensures grey_reached m' o) (decreases p)
  = match p with
    | WGrey _ _ ->
      ag_hd m m' o;
      let p' : wpath m' o = WGrey o () in ()
    | WStep x _ p0 _ ->
      ag_wpath m m' x p0;
      ag_edge m m' x o;
      ag_hd m m' o;
      let p0' = FStar.IndefiniteDescription.indefinite_description_ghost (wpath m' x) (fun _ -> True) in
      let p' : wpath m' o = WStep x o p0' () in ()

let ag_grey_reached (m m': mheap) (o: nat)
  : Lemma (requires agree m m') (ensures grey_reached m o ==> grey_reached m' o)
  = let f (p: wpath m o) : Lemma (grey_reached m' o) = ag_wpath m m' o p in
    C.forall_intro f

let ag_tricolour (m m': mheap) (snap allocd: nat -> prop)
  : Lemma (requires agree m m' /\ tricolour m snap allocd) (ensures tricolour m' snap allocd)
  = C.forall_intro (fun (o: nat) -> ag_hd m m' o);
    C.forall_intro (C.move_requires (ag_grey_reached m m'))

let ag_closed1 (m m': mheap) (live: nat -> prop) (o i a: nat)
  : Lemma (requires agree m m' /\ closed m live /\ live o /\ ptr_field m' o i /\ field m' o i == VPtr (Major a))
          (ensures exists (o': nat). resolve m' a == Some o' /\ live o')
  = agree_sym m m';
    ag_hd m m' o; ag_field m' m o i; ag_resolve m m' a;
    assert (ptr_field m o i /\ field m o i == VPtr (Major a));
    assert (exists (o': nat). resolve m a == Some o' /\ live o')

let ag_closed (m m': mheap) (live: nat -> prop)
  : Lemma (requires agree m m' /\ closed m live) (ensures closed m' live)
  = C.forall_intro_3 (fun o i a -> C.move_requires (ag_closed1 m m' live o i) a)

let ag_white_live (m m': mheap) (live: nat -> prop) (o: nat)
  : Lemma (requires agree m m')
          (ensures (white_live m live o <==> white_live m' live o) /\ (grey_live m live o <==> grey_live m' live o))
  = ag_hd m m' o

/// The measures, read on agreeing heaps (both sides).
let ag_decreases (m1 m2 m1' m2': mheap) (live: nat -> prop)
  : Lemma (requires agree m1 m1' /\ agree m2 m2')
          (ensures (mark_decreases m1 m2 live ==> mark_decreases m1' m2' live) /\
                   (mark_no_increase m1 m2 live ==> mark_no_increase m1' m2' live))
  = C.forall_intro (fun (o: nat) -> ag_white_live m1 m1' live o);
    C.forall_intro (fun (o: nat) -> ag_white_live m2 m2' live o)

/// ---------------------------------------------------------------------------
/// Configurations
/// ---------------------------------------------------------------------------

let yrepr_agree (#t #yt: Type0) (r: rep t yt) (m1 m2: mheap) (y: yt)
  : Lemma (requires faithful_young r /\ r.yrepr m1 y /\ r.yrepr m2 y) (ensures agree m1 m2)
  = let aux (w: nat) (o: nat)
      : Lemma (requires covers m2 o w /\ o < w) (ensures m1.body w == m2.body w)
      = assert (r.yread y o (w - o - 1) == field m2 o (w - o - 1));
        assert (r.yhd y o == m1.hd o);
        assert (r.yread y o (w - o - 1) == field m1 o (w - o - 1)) in
    let aux' (w: nat) : Lemma (field_word m2 w ==> m1.body w == m2.body w)
      = C.forall_intro (C.move_requires (aux w)) in
    C.forall_intro aux'

/// Two worlds that represent one collector's world agree.
let views_agree (#t #yt: Type0) (r: rep t yt) (cw: cworld t yt) (w1 w2: world)
  : Lemma (requires faithful r /\ cviews r cw w1 /\ cviews r cw w2) (ensures wagree w1 w2)
  = repr_agree r w1.maj w2.maj cw.cmaj;
    yrepr_agree r w1.yng w2.yng cw.cyng

/// **Any world that views a configuration agrees with `vw x`.**
let vw_agree (#c: comps) (x: config c) (w: world)
  : Lemma (requires faithful c.r /\ views x w) (ensures has_view x /\ wagree w (vw x))
  = vw_views x;
    views_agree c.r x.w w (vw x)
