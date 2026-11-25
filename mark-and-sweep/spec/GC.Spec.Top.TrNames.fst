/// ---------------------------------------------------------------------------
/// GC.Spec.Top.TrNames - when the reference program names only what it reaches
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  T1's part 2 assumes `Transp.names_reachable prog` of the
/// reference program a run is transparent with.  `names_of`: if every
/// program event of the run names only blocks reached from the roots
/// (`enamed`: a pointer to a block on a path of major fields from a root, or
/// a young root), then every reference program the run is transparent with
/// names only what it reaches.  Its reference objects are the renamed
/// blocks, and a path from a root is a path in the reference store
/// (`rp_rreach`).

module GC.Spec.Top.TrNames

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Transp
module L = FStar.List.Tot
module RF = GC.Spec.Top.RunFacts

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Reached from the roots
/// ---------------------------------------------------------------------------

noeq type rp (w: world) : nat -> Type0 =
  | PRoot : o:nat -> a:nat -> squash (L.memP (VPtr (Major a)) w.roots /\ resolve w.maj a == Some o) -> rp w o
  | PStep : o:nat -> o':nat -> rp w o -> squash (major_edge w.maj o o') -> rp w o'

let rooted (w: world) (o: nat) : prop = exists (_: rp w o). True

/// A value the program names: a word, a pointer to a block reached from the
/// roots, or a young root.
let vnamed (w: world) (v: value) : prop =
  match v with
  | VInt _ -> True
  | VPtr (Major a) -> exists (o: nat). resolve w.maj a == Some o /\ rooted w o
  | VPtr (Young a) -> L.memP (VPtr (Young a)) w.roots /\ Some? (resolve w.yng a)

/// A program event names only such values and blocks.
let enamed (w: world) (e: event) : prop =
  match e with
  | EAlloc _ _ vs -> forall (v: value). L.memP v vs ==> vnamed w v
  | EYoungAlloc _ _ vs -> forall (v: value). L.memP v vs ==> vnamed w v
  | EWrite (Major o) _ v -> rooted w o /\ vnamed w v
  | EWrite (Young _) _ _ -> False
  | ERead (Major o) _ -> rooted w o
  | ERead (Young _) _ -> False
  | ERoots rs -> forall (v: value). L.memP v rs ==> vnamed w v
  | _ -> True

/// Reached from the roots: reachable.
let rec rp_reach (w: world) (o: nat) (p: rp w o) : Tot (reach w o) (decreases p)
  = match p with
    | PRoot _ a _ -> RBase o ()
    | PStep o0 _ p0 _ -> RStep o0 o (rp_reach w o0 p0) ()

let rooted_reachable (w: world) (o: nat) : Lemma (requires rooted w o) (ensures reachable w o)
  = eliminate exists (p: rp w o). True
    with (let r = rp_reach w o p in assert (reachable w o))

/// One step more.
let rooted_root (w: world) (a o: nat)
  : Lemma (requires L.memP (VPtr (Major a)) w.roots /\ resolve w.maj a == Some o) (ensures rooted w o)
  = let p : rp w o = PRoot o a () in assert (rooted w o)

let rooted_step (w: world) (o o': nat)
  : Lemma (requires rooted w o /\ major_edge w.maj o o') (ensures rooted w o')
  = eliminate exists (p: rp w o). True
    with (let p' : rp w o' = PStep o o' p () in assert (rooted w o'))

/// The same reading, the same roots: the same blocks reached.
let rec rp_wheq (w w': world) (o: nat) (p: rp w o)
  : Ghost (rp w' o) (requires RF.wheq w w') (ensures fun _ -> True) (decreases p)
  = match p with
    | PRoot _ a _ -> assert (resolve w.maj a == resolve w'.maj a); PRoot o a ()
    | PStep o0 _ p0 _ -> RF.edge_wheq w.maj w'.maj o0 o; PStep o0 o (rp_wheq w w' o0 p0) ()

let rooted_wheq (w w': world) (o: nat)
  : Lemma (requires RF.wheq w w' /\ rooted w o) (ensures rooted w' o)
  = eliminate exists (p: rp w o). True
    with (let p' = rp_wheq w w' o p in assert (rooted w' o))

let vnamed_wheq (w w': world) (v: value)
  : Lemma (requires RF.wheq w w' /\ vnamed w v) (ensures vnamed w' v)
  = match v with
    | VPtr (Major a) ->
      eliminate exists (o: nat). resolve w.maj a == Some o /\ rooted w o
      with (rooted_wheq w w' o; assert (resolve w.maj a == resolve w'.maj a))
    | VPtr (Young a) -> assert (resolve w.yng a == resolve w'.yng a)
    | _ -> ()

let enamed_wheq (w w': world) (e: event)
  : Lemma (requires RF.wheq w w' /\ enamed w e) (ensures enamed w' e)
  = match e with
    | EWrite (Major o) _ v -> rooted_wheq w w' o; vnamed_wheq w w' v
    | ERead (Major o) _ -> rooted_wheq w w' o
    | EAlloc _ _ vs -> FStar.Classical.forall_intro (FStar.Classical.move_requires (vnamed_wheq w w'))
    | EYoungAlloc _ _ vs -> FStar.Classical.forall_intro (FStar.Classical.move_requires (vnamed_wheq w w'))
    | ERoots vs -> FStar.Classical.forall_intro (FStar.Classical.move_requires (vnamed_wheq w w'))
    | _ -> ()

/// ---------------------------------------------------------------------------
/// In the reference store
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec mem_idx (#t: Type) (v: t) (l: list t)
  : Lemma (requires L.memP v l) (ensures exists (j: nat). j < L.length l /\ L.index l j == v) (decreases l)
  = match l with
    | h :: tl ->
      if FStar.IndefiniteDescription.strong_excluded_middle (v == h) then assert (L.index l 0 == h)
      else begin
        mem_idx v tl;
        eliminate exists (j: nat). j < L.length tl /\ L.index tl j == v
        with assert (L.index l (j + 1) == v)
      end
#pop-options

/// A root's reference value is a root of the store.
let root_rref (#c: comps) (rn: renaming) (x: config c) (r: rstore) (v: value)
  : Lemma (requires scorr rn x r /\ L.memP v (wv x).roots)
          (ensures exists (rv: rval). L.memP rv r.rroots /\ vcorr rn (wv x) true v rv)
  = mem_idx v (wv x).roots;
    eliminate exists (j: nat). j < L.length (wv x).roots /\ L.index (wv x).roots j == v
    with L.lemma_index_memP r.rroots j

/// The reference object a visible block holds.
let held (#c: comps) (rn: renaming) (x: config c) (r: rstore) (p: ptr) (k: nat)
  : Lemma (requires scorr rn x r /\ visible (wv x) p /\ rn k == Some p)
          (ensures Some? (r.objs k) /\ ocorr rn (wv x) p (Some?.v (r.objs k)))
  = eliminate exists (k2: nat). rn k2 == Some p /\ Some? (r.objs k2) /\ ocorr rn (wv x) p (Some?.v (r.objs k2))
    with ()

/// From a root.
let root_rreach (#c: comps) (rn: renaming) (x: config c) (r: rstore) (a o k: nat)
  : Lemma (requires scorr rn x r /\ L.memP (VPtr (Major a)) (wv x).roots /\ resolve (wv x).maj a == Some o /\
                    reachable (wv x) o /\ rn k == Some (Major o))
          (ensures rreachable r k)
  = root_rref rn x r (VPtr (Major a));
    eliminate exists (rv: rval). L.memP rv r.rroots /\ vcorr rn (wv x) true (VPtr (Major a)) rv
    with begin
      let RPtr k' d = rv in
      held rn x r (Major o) k';
      let q : rreach r k' = RRoot k' d () in
      assert (rreachable r k')
    end

/// Along a field.
#push-options "--z3rlimit 40"
let field_rreach (#c: comps) (rn: renaming) (x: config c) (r: rstore) (o o' k k': nat)
  : Lemma (requires scorr rn x r /\ reachable (wv x) o /\ reachable (wv x) o' /\ major_edge (wv x).maj o o' /\
                    rn k == Some (Major o) /\ rreachable r k /\ rn k' == Some (Major o'))
          (ensures rreachable r k')
  = let w = wv x in
    held rn x r (Major o) k;
    let ro = Some?.v (r.objs k) in
    eliminate exists (i a: nat). ptr_field w.maj o i /\ field w.maj o i == VPtr (Major a) /\ resolve w.maj a == Some o'
    with begin
      assert (vcorr rn w (scannable ro.rtag) (field w.maj o i) (ro.rf i));
      let RPtr k2 d = ro.rf i in
      held rn x r (Major o') k2;
      eliminate exists (q: rreach r k). True
      with begin
        let q' : rreach r k2 = RNext k k2 i d q () in
        assert (rreachable r k2)
      end
    end
#pop-options

/// **A block reached from the roots holds a reachable reference object.**
let rec rp_rreach (#c: comps) (rn: renaming) (x: config c) (r: rstore) (o: nat) (p: rp (wv x) o) (k: nat)
  : Lemma (requires scorr rn x r /\ rn k == Some (Major o)) (ensures rreachable r k) (decreases p)
  = let w = wv x in
    let q = rp_reach w o p in
    assert (reachable w o);
    match p with
    | PRoot _ a _ -> root_rreach rn x r a o k
    | PStep o0 _ p0 _ ->
      let q0 = rp_reach w o0 p0 in
      assert (reachable w o0);
      assert (visible w (Major o0));
      eliminate exists (k0: nat). rn k0 == Some (Major o0) /\ Some? (r.objs k0) /\
                                  ocorr rn w (Major o0) (Some?.v (r.objs k0))
      with begin
        rp_rreach rn x r o0 p0 k0;
        field_rreach rn x r o0 o k0 k
      end

let rooted_rreach (#c: comps) (rn: renaming) (x: config c) (r: rstore) (o k: nat)
  : Lemma (requires scorr rn x r /\ rooted (wv x) o /\ rn k == Some (Major o)) (ensures rreachable r k)
  = eliminate exists (p: rp (wv x) o). True
    with rp_rreach rn x r o p k

/// From a young root.
let yroot_rreach (#c: comps) (rn: renaming) (x: config c) (r: rstore) (a y k: nat)
  : Lemma (requires scorr rn x r /\ L.memP (VPtr (Young a)) (wv x).roots /\ resolve (wv x).yng a == Some y /\
                    rn k == Some (Young y))
          (ensures rreachable r k)
  = let w = wv x in
    let yq : yreach w y = YRoot y a () in
    assert (yreachable w y);
    root_rref rn x r (VPtr (Young a));
    eliminate exists (rv: rval). L.memP rv r.rroots /\ vcorr rn w true (VPtr (Young a)) rv
    with begin
      let RPtr k' d = rv in
      held rn x r (Young y) k';
      let q : rreach r k' = RRoot k' d () in
      assert (rreachable r k')
    end

/// A named value's reference value names a reachable object.
let val_reach (#c: comps) (rn: renaming) (x: config c) (r: rstore) (scan: bool) (v: value) (rv: rval)
  : Lemma (requires scorr rn x r /\ vcorr rn (wv x) scan v rv /\ vnamed (wv x) v) (ensures rval_reach r rv)
  = match rv with
    | RWord _ -> ()
    | RPtr k d ->
      match v with
      | VPtr (Major a) ->
        eliminate exists (o: nat). resolve (wv x).maj a == Some o /\ rooted (wv x) o
        with rooted_rreach rn x r o k
      | VPtr (Young a) ->
        eliminate exists (y: nat). rn k == Some (Young y) /\ a == y + d /\ resolve (wv x).yng a == Some y
        with yroot_rreach rn x r a y k

let list_all (#c: comps) (rn: renaming) (x: config c) (r: rstore) (scan: bool) (vs: list value) (rvs: list rval)
  : Lemma (requires scorr rn x r /\ vcorr_list rn (wv x) scan vs rvs /\ (forall (v: value). L.memP v vs ==> vnamed (wv x) v))
          (ensures forall (i: nat). i < L.length rvs ==> rval_reach r (L.index rvs i))
  = let f (i: nat) : Lemma (i < L.length rvs ==> rval_reach r (L.index rvs i))
      = if i < L.length rvs then begin
          L.lemma_index_memP vs i;
          val_reach rn x r scan (L.index vs i) (L.index rvs i)
        end in
    FStar.Classical.forall_intro f

let list_reach (#c: comps) (rn: renaming) (x: config c) (r: rstore) (scan: bool) (vs: list value) (rvs: list rval) (i: nat)
  : Lemma (requires scorr rn x r /\ vcorr_list rn (wv x) scan vs rvs /\ (forall (v: value). L.memP v vs ==> vnamed (wv x) v) /\
                    i < L.length rvs)
          (ensures rval_reach r (L.index rvs i))
  = L.lemma_index_memP vs i;
    val_reach rn x r scan (L.index vs i) (L.index rvs i)

/// **A named event's reference event names reachable objects.**
#push-options "--z3rlimit 40"
let ev_names (#c: comps) (rn: renaming) (x: config c) (r: rstore) (e: event) (re: revent)
  : Lemma (requires scorr rn x r /\ ev_corr rn (wv x) r e re /\ enamed (wv x) e) (ensures names_reach r re)
  = match e, re with
    | EAlloc sz tag vs, RAlloc _ _ rvs -> list_all rn x r (scannable tag) vs rvs
    | EYoungAlloc sz tag vs, RAlloc _ _ rvs -> list_all rn x r (scannable tag) vs rvs
    | EWrite (Major o) i v, RWrite k _ rv ->
      rooted_rreach rn x r o k;
      val_reach rn x r (scannable (robj_of r k).rtag) v rv
    | ERead (Major o) i, RRead k _ -> rooted_rreach rn x r o k
    | ERoots vs, RRoots rvs ->
      let one (u: rval) : Lemma (L.memP u rvs ==> rval_reach r u)
        = if FStar.IndefiniteDescription.strong_excluded_middle (L.memP u rvs) then begin
            mem_idx u rvs;
            list_all rn x r true vs rvs
          end in
      FStar.Classical.forall_intro one
    | _, _ -> ()
#pop-options

/// **The reference program names only what it reaches**, when the run's
/// program events name only blocks reached from the roots.
let names_of (c: comps) (n ny: nat) (es: list event) (prog: list revent) (io: nat -> renaming)
  : Lemma (requires transparent c n ny es prog io /\
                    (forall (i: nat). i < L.length es /\ is_mutator_event (ev es i) ==> enamed (wv (at c n ny es i)) (ev es i)))
          (ensures names_reachable prog)
  = let one (m: nat) : Lemma (m < L.length prog ==> names_reach (rat prog m) (rev_at prog m))
      = if m < L.length prog then begin
          GC.Spec.Top.T1Rep.mc_hit es (L.length es) m;
          eliminate exists (i: nat). i < L.length es /\ is_mutator_event (ev es i) /\ mc es i == m
          with ev_names (io i) (at c n ny es i) (rat prog m) (ev es i) (rev_at prog m)
        end in
    FStar.Classical.forall_intro one
