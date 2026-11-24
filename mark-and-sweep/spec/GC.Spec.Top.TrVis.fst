/// ---------------------------------------------------------------------------
/// GC.Spec.Top.TrVis - visible blocks, and the correspondence's shape
/// ---------------------------------------------------------------------------
///
/// Design doc §16.15.  The visible blocks hold the roots' targets and are
/// closed under fields (`vis_root`, `vis_field`, `vis_young`); any set with
/// those properties holds them (`vis_sub`).  The last clause of `scorr`
/// (every reachable reference object is in a visible block) follows from
/// the others (`scorr_intro`).  A renaming can be cut down to the visible
/// blocks and the store's names (`restrict`, `clean`), keeping `scorr`.

module GC.Spec.Top.TrVis

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Transp
open GC.Spec.Top.TrRef
module L = FStar.List.Tot
module C = FStar.Classical
module ID = FStar.IndefiniteDescription

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Blocks and targets
/// ---------------------------------------------------------------------------

let ph (w: world) (p: ptr) : mheap = match p with Major _ -> w.maj | Young _ -> w.yng
let pa (p: ptr) : nat = match p with Major o -> o | Young o -> o

/// The block a value points to.
let target (w: world) (v: value) : option ptr =
  match v with
  | VPtr (Major a) -> (match resolve w.maj a with Some o -> Some (Major o) | None -> None)
  | VPtr (Young a) -> (match resolve w.yng a with Some o -> Some (Young o) | None -> None)
  | VInt _ -> None

/// A pointer field of block `p` (a field of a scannable block).
let pfield (w: world) (p: ptr) (i: nat) : prop = ptr_field (ph w p) (pa p) i
let fld (w: world) (p: ptr) (i: nat) : value = field (ph w p) (pa p) i

/// ---------------------------------------------------------------------------
/// Visible blocks are closed
/// ---------------------------------------------------------------------------

let reach_of (w: world) (o: nat) : Lemma (requires reachable w o) (ensures True) = ()

let get_reach (w: world) (o: nat) : Ghost (reach w o) (requires reachable w o) (ensures fun _ -> True)
  = ID.indefinite_description_ghost (reach w o) (fun _ -> True)

let get_yreach (w: world) (y: nat) : Ghost (yreach w y) (requires yreachable w y) (ensures fun _ -> True)
  = ID.indefinite_description_ghost (yreach w y) (fun _ -> True)

let reached (w: world) (o: nat) (r: reach w o) : Lemma (reachable w o)
  = C.exists_intro (fun (_: reach w o) -> True) r

let yreached (w: world) (y: nat) (r: yreach w y) : Lemma (yreachable w y)
  = C.exists_intro (fun (_: yreach w y) -> True) r

let vis_root (w: world) (v: value) (q: ptr)
  : Lemma (requires L.memP v w.roots /\ target w v == Some q) (ensures visible w q)
  = match v with
    | VPtr (Major a) ->
      (match resolve w.maj a with
       | Some o -> reached w o (RBase o ())
       | None -> ())
    | VPtr (Young a) ->
      (match resolve w.yng a with
       | Some y -> yreached w y (YRoot y a ())
       | None -> ())
    | _ -> ()

/// A major target of any young block's field is visible.
let vis_young (w: world) (y i: nat) (q: ptr)
  : Lemma (requires ptr_field w.yng y i /\ target w (field w.yng y i) == Some q /\ Major? q)
          (ensures visible w q)
  = match field w.yng y i with
    | VPtr (Major a) ->
      (match resolve w.maj a with
       | Some o -> reached w o (RBase o ())
       | None -> ())
    | _ -> ()

let vis_field (w: world) (p: ptr) (i: nat) (q: ptr)
  : Lemma (requires visible w p /\ pfield w p i /\ target w (fld w p i) == Some q) (ensures visible w q)
  = match p with
    | Major o ->
      let r = get_reach w o in
      (match field w.maj o i with
       | VPtr (Major a) ->
         (match resolve w.maj a with Some o' -> reached w o' (RStep o o' r ()) | None -> ())
       | VPtr (Young a) ->
         (match resolve w.yng a with Some y -> yreached w y (YOld y o i a r ()) | None -> ())
       | _ -> ())
    | Young y ->
      let r = get_yreach w y in
      (match field w.yng y i with
       | VPtr (Young a) ->
         (match resolve w.yng a with Some y' -> yreached w y' (YStep y y' r ()) | None -> ())
       | VPtr (Major a) -> vis_young w y i q
       | _ -> ())

/// ---------------------------------------------------------------------------
/// Any closed set holds the visible blocks
/// ---------------------------------------------------------------------------

let vclosed (w: world) (s: ptr -> prop) : prop =
  (forall (v: value) (q: ptr). L.memP v w.roots /\ target w v == Some q ==> s q) /\
  (forall (y i: nat) (q: ptr). ptr_field w.yng y i /\ target w (field w.yng y i) == Some q /\ Major? q ==> s q) /\
  (forall (p: ptr) (i: nat) (q: ptr). s p /\ pfield w p i /\ target w (fld w p i) == Some q ==> s q)

let vc_root (w: world) (s: ptr -> prop) (v: value) (q: ptr)
  : Lemma (requires vclosed w s /\ L.memP v w.roots /\ target w v == Some q) (ensures s q) = ()

let vc_young (w: world) (s: ptr -> prop) (y i: nat) (q: ptr)
  : Lemma (requires vclosed w s /\ ptr_field w.yng y i /\ target w (field w.yng y i) == Some q /\ Major? q)
          (ensures s q) = ()

let vc_field (w: world) (s: ptr -> prop) (p: ptr) (i: nat) (q: ptr)
  : Lemma (requires vclosed w s /\ s p /\ pfield w p i /\ target w (fld w p i) == Some q) (ensures s q) = ()

let vs_base (w: world) (s: ptr -> prop) (o: nat)
  : Lemma (requires vclosed w s /\ outside_ref w o) (ensures s (Major o))
  = if ID.strong_excluded_middle (root_ref w o) then
      eliminate exists (a: nat). L.memP (VPtr (Major a)) w.roots /\ resolve w.maj a == Some o
      with vc_root w s (VPtr (Major a)) (Major o)
    else
      eliminate exists (y i a: nat). ptr_field w.yng y i /\ field w.yng y i == VPtr (Major a) /\
                                     resolve w.maj a == Some o
      with vc_young w s y i (Major o)

let vs_edge (w: world) (s: ptr -> prop) (o o': nat)
  : Lemma (requires vclosed w s /\ s (Major o) /\ major_edge w.maj o o') (ensures s (Major o'))
  = eliminate exists (i a: nat). ptr_field w.maj o i /\ field w.maj o i == VPtr (Major a) /\ resolve w.maj a == Some o'
    with vc_field w s (Major o) i (Major o')

let vs_yedge (w: world) (s: ptr -> prop) (y y': nat)
  : Lemma (requires vclosed w s /\ s (Young y) /\ young_edge w.yng y y') (ensures s (Young y'))
  = eliminate exists (i a: nat). ptr_field w.yng y i /\ field w.yng y i == VPtr (Young a) /\ resolve w.yng a == Some y'
    with vc_field w s (Young y) i (Young y')

let rec vs_reach (w: world) (s: ptr -> prop) (o: nat) (r: reach w o)
  : Lemma (requires vclosed w s) (ensures s (Major o)) (decreases r)
  = match r with
    | RBase _ _ -> vs_base w s o
    | RStep o0 _ r0 _ -> vs_reach w s o0 r0; vs_edge w s o0 o

let rec vs_yreach (w: world) (s: ptr -> prop) (y: nat) (r: yreach w y)
  : Lemma (requires vclosed w s) (ensures s (Young y)) (decreases r)
  = match r with
    | YRoot _ a _ -> vc_root w s (VPtr (Young a)) (Young y)
    | YOld _ o i a r0 _ -> vs_reach w s o r0; vc_field w s (Major o) i (Young y)
    | YStep y0 _ r0 _ -> vs_yreach w s y0 r0; vs_yedge w s y0 y

let vis_sub1 (w: world) (s: ptr -> prop) (p: ptr)
  : Lemma (requires vclosed w s /\ visible w p) (ensures s p)
  = match p with
    | Major o -> vs_reach w s o (get_reach w o)
    | Young y -> vs_yreach w s y (get_yreach w y)

/// **The visible blocks are in every closed set.**
let vis_sub (w: world) (s: ptr -> prop)
  : Lemma (requires vclosed w s) (ensures forall (p: ptr). visible w p ==> s p)
  = C.forall_intro (C.move_requires (vis_sub1 w s))

/// ---------------------------------------------------------------------------
/// The correspondence, by parts
/// ---------------------------------------------------------------------------

let roots_corr (rn: renaming) (w: world) (r: rstore) : prop =
  L.length w.roots == L.length r.rroots /\
  (forall (i: nat). i < L.length w.roots ==> vcorr rn w true (L.index w.roots i) (L.index r.rroots i))

let cover (rn: renaming) (w: world) (r: rstore) : prop =
  forall (p: ptr). visible w p ==>
    (exists (k: nat). rn k == Some p /\ Some? (r.objs k) /\ ocorr rn w p (Some?.v (r.objs k)))

let inj (rn: renaming) (w: world) : prop =
  forall (k k': nat) (p: ptr). rn k == Some p /\ rn k' == Some p /\ visible w p ==> k == k'

let rvis (rn: renaming) (w: world) (r: rstore) : prop =
  forall (k: nat). rreachable r k ==> (exists (p: ptr). rn k == Some p /\ visible w p)

let scorr_w (rn: renaming) (w: world) (r: rstore) : prop =
  roots_corr rn w r /\ cover rn w r /\ inj rn w /\ rvis rn w r

let scorr_eq (#c: comps) (rn: renaming) (x: config c) (r: rstore)
  : Lemma (scorr rn x r <==> scorr_w rn (wv x) r) = ()

/// The renaming has no stale names: each is a visible block, and a name of
/// the store.
let clean (rn: renaming) (w: world) (r: rstore) : prop =
  forall (k: nat) (p: ptr). rn k == Some p ==> visible w p /\ k < r.next

/// ---------------------------------------------------------------------------
/// Values
/// ---------------------------------------------------------------------------

let vcorr_ptr (rn: renaming) (w: world) (scan: bool) (v: value) (k d: nat)
  : Lemma (requires vcorr rn w scan v (RPtr k d)) (ensures scan /\ Some? (rn k) /\ target w v == rn k)
  = ()

/// `vcorr` reads `rn` only at the pointer's object.
let vcorr_same (rn rn': renaming) (w: world) (scan: bool) (v: value) (rv: rval)
  : Lemma (requires vcorr rn w scan v rv /\ (match rv with RPtr k _ -> rn' k == rn k | _ -> True))
          (ensures vcorr rn' w scan v rv)
  = ()

let rec memP_idx (#t: Type) (x: t) (l: list t)
  : Lemma (requires L.memP x l) (ensures exists (i: nat). i < L.length l /\ L.index l i == x) (decreases l)
  = match l with
    | h :: tl ->
      if ID.strong_excluded_middle (x == h) then assert (L.index l 0 == x)
      else begin
        memP_idx x tl;
        eliminate exists (i: nat). i < L.length tl /\ L.index tl i == x
        with assert (L.index l (i + 1) == x)
      end

let rec idx_memP (#t: Type) (l: list t) (i: nat)
  : Lemma (requires i < L.length l) (ensures L.memP (L.index l i) l) (decreases l)
  = match l with _ :: tl -> if i = 0 then () else idx_memP tl (i - 1)

/// ---------------------------------------------------------------------------
/// The last clause from the others
/// ---------------------------------------------------------------------------

let rroot_vis (rn: renaming) (w: world) (r: rstore) (k d: nat)
  : Lemma (requires roots_corr rn w r /\ L.memP (RPtr k d) r.rroots)
          (ensures exists (p: ptr). rn k == Some p /\ visible w p)
  = memP_idx (RPtr k d) r.rroots;
    eliminate exists (j: nat). j < L.length r.rroots /\ L.index r.rroots j == RPtr k d
    with begin
      let v = L.index w.roots j in
      vcorr_ptr rn w true v k d;
      idx_memP w.roots j;
      vis_root w v (Some?.v (rn k))
    end

let rnext_vis (rn: renaming) (w: world) (r: rstore) (k k' i d: nat)
  : Lemma (requires cover rn w r /\ inj rn w /\ (exists (p: ptr). rn k == Some p /\ visible w p) /\
                    rptr_field r k i /\ (Some?.v (r.objs k)).rf i == RPtr k' d)
          (ensures exists (p: ptr). rn k' == Some p /\ visible w p)
  = let p = Some?.v (rn k) in
    eliminate exists (k1: nat). rn k1 == Some p /\ Some? (r.objs k1) /\ ocorr rn w p (Some?.v (r.objs k1))
    with begin
      assert (k1 == k);
      let ro = Some?.v (r.objs k) in
      assert (vcorr rn w (scannable ro.rtag) (fld w p i) (ro.rf i));
      vcorr_ptr rn w (scannable ro.rtag) (fld w p i) k' d;
      vis_field w p i (Some?.v (rn k'))
    end

let rec rreach_vis (rn: renaming) (w: world) (r: rstore) (k: nat) (rr: rreach r k)
  : Lemma (requires roots_corr rn w r /\ cover rn w r /\ inj rn w)
          (ensures exists (p: ptr). rn k == Some p /\ visible w p) (decreases rr)
  = match rr with
    | RRoot _ d _ -> rroot_vis rn w r k d
    | RNext k0 _ i d rr0 _ -> rreach_vis rn w r k0 rr0; rnext_vis rn w r k0 k i d

let rvis_of (rn: renaming) (w: world) (r: rstore) (k: nat)
  : Lemma (requires roots_corr rn w r /\ cover rn w r /\ inj rn w /\ rreachable r k)
          (ensures exists (p: ptr). rn k == Some p /\ visible w p)
  = eliminate exists (rr: rreach r k). True
    with rreach_vis rn w r k rr

/// **`scorr` from roots, cover and injectivity.**
let scorr_intro (rn: renaming) (w: world) (r: rstore)
  : Lemma (requires roots_corr rn w r /\ cover rn w r /\ inj rn w) (ensures scorr_w rn w r)
  = C.forall_intro (C.move_requires (rvis_of rn w r))

/// ---------------------------------------------------------------------------
/// Cutting a renaming down
/// ---------------------------------------------------------------------------

let cut (w: world) (rn: renaming) (k: nat) : GTot (option ptr) =
  match rn k with
  | Some p -> if ID.strong_excluded_middle (visible w p) then Some p else None
  | None -> None

let restrict (w: world) (rn: renaming) (n: nat) : GTot renaming =
  let s = Seq.init_ghost n (fun (k: nat{k < n}) -> cut w rn k) in
  (fun (k: nat) -> if k < Seq.length s then Seq.index s k else None)

let restrict_spec (w: world) (rn: renaming) (n k: nat)
  : Lemma (restrict w rn n k == (if k < n then cut w rn k else None))
  = Seq.init_ghost_index n (fun (k: nat{k < n}) -> cut w rn k)

let restrict_some (w: world) (rn: renaming) (n k: nat) (p: ptr)
  : Lemma (restrict w rn n k == Some p <==> (k < n /\ rn k == Some p /\ visible w p))
  = restrict_spec w rn n k

/// A visible name of a store with `scorr` is one of its names.
let name_ok (rn: renaming) (w: world) (r: rstore) (k: nat) (p: ptr)
  : Lemma (requires cover rn w r /\ inj rn w /\ rwf r /\ rn k == Some p /\ visible w p) (ensures k < r.next)
  = eliminate exists (k1: nat). rn k1 == Some p /\ Some? (r.objs k1) /\ ocorr rn w p (Some?.v (r.objs k1))
    with assert (k1 == k)

let keep_name (rn: renaming) (w: world) (r: rstore) (k: nat) (p: ptr)
  : Lemma (requires cover rn w r /\ inj rn w /\ rwf r /\ rn k == Some p /\ visible w p)
          (ensures restrict w rn r.next k == Some p)
  = name_ok rn w r k p;
    restrict_some w rn r.next k p

/// A value whose target is visible keeps its correspondence.
let vcorr_cut (rn: renaming) (w: world) (r: rstore) (scan: bool) (v: value) (rv: rval)
  : Lemma (requires cover rn w r /\ inj rn w /\ rwf r /\ vcorr rn w scan v rv /\
                    (RPtr? rv ==> (forall (q: ptr). target w v == Some q ==> visible w q)))
          (ensures vcorr (restrict w rn r.next) w scan v rv)
  = match rv with
    | RPtr k d ->
      vcorr_ptr rn w scan v k d;
      keep_name rn w r k (Some?.v (rn k));
      vcorr_same rn (restrict w rn r.next) w scan v rv
    | _ -> ()

let cut_root (rn: renaming) (w: world) (r: rstore) (j: nat)
  : Lemma (requires scorr_w rn w r /\ rwf r /\ j < L.length w.roots)
          (ensures vcorr (restrict w rn r.next) w true (L.index w.roots j) (L.index r.rroots j))
  = idx_memP w.roots j;
    C.forall_intro (C.move_requires (vis_root w (L.index w.roots j)));
    vcorr_cut rn w r true (L.index w.roots j) (L.index r.rroots j)

let cut_field (rn: renaming) (w: world) (r: rstore) (p: ptr) (ro: robj) (i: nat)
  : Lemma (requires scorr_w rn w r /\ rwf r /\ visible w p /\ ocorr rn w p ro /\ i < ro.rsz)
          (ensures vcorr (restrict w rn r.next) w (scannable ro.rtag) (fld w p i) (ro.rf i))
  = let aux (q: ptr) : Lemma (requires RPtr? (ro.rf i) /\ target w (fld w p i) == Some q) (ensures visible w q)
      = vis_field w p i q in
    C.forall_intro (C.move_requires aux);
    vcorr_cut rn w r (scannable ro.rtag) (fld w p i) (ro.rf i)

let cut_cover1 (rn: renaming) (w: world) (r: rstore) (p: ptr)
  : Lemma (requires scorr_w rn w r /\ rwf r /\ visible w p)
          (ensures exists (k: nat). restrict w rn r.next k == Some p /\ Some? (r.objs k) /\
                                    ocorr (restrict w rn r.next) w p (Some?.v (r.objs k)))
  = eliminate exists (k: nat). rn k == Some p /\ Some? (r.objs k) /\ ocorr rn w p (Some?.v (r.objs k))
    with begin
      keep_name rn w r k p;
      let ro = Some?.v (r.objs k) in
      C.forall_intro (C.move_requires (cut_field rn w r p ro))
    end

let cut_rvis (rn: renaming) (w: world) (r: rstore) (k: nat)
  : Lemma (requires scorr_w rn w r /\ rwf r /\ rreachable r k)
          (ensures exists (p: ptr). restrict w rn r.next k == Some p /\ visible w p)
  = eliminate exists (p: ptr). rn k == Some p /\ visible w p
    with keep_name rn w r k p

/// **Cut down to the visible blocks, a renaming keeps `scorr` and is clean.**
let restrict_scorr (rn: renaming) (w: world) (r: rstore)
  : Lemma (requires scorr_w rn w r /\ rwf r)
          (ensures scorr_w (restrict w rn r.next) w r /\ clean (restrict w rn r.next) w r)
  = let rn' = restrict w rn r.next in
    let f (j: nat)
      : Lemma (j < L.length w.roots ==> vcorr rn' w true (L.index w.roots j) (L.index r.rroots j))
      = if j < L.length w.roots then cut_root rn w r j in
    C.forall_intro f;
    C.forall_intro (C.move_requires (cut_cover1 rn w r));
    C.forall_intro_2 (fun (k: nat) (p: ptr) -> restrict_some w rn r.next k p);
    C.forall_intro (C.move_requires (cut_rvis rn w r))
