/// ---------------------------------------------------------------------------
/// GC.Spec.Top.TrMinA - the correspondence across a minor collection: the
/// reference side
/// ---------------------------------------------------------------------------
///
/// Design doc §16.15.  A minor collection moves every visible young block to
/// its copy and leaves every visible major block in place (`fmu`); each
/// field and root is forwarded (`fwdv`), and points where it pointed,
/// moved (`fwd_moved`).  The reference store does not change; the renaming
/// follows the blocks (`minor_ref`).

module GC.Spec.Top.TrMinA

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Transp
open GC.Spec.Top.TrRef
open GC.Spec.Top.TrVis
open GC.Spec.Top.TrGen
module L = FStar.List.Tot
module C = FStar.Classical
module ID = FStar.IndefiniteDescription

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// Where a block goes: a forwarded young block to its copy.
let fmu (fwd: nat -> option nat) (p: ptr) : ptr =
  match p with
  | Young y -> (match fwd y with Some cp -> Major cp | None -> p)
  | Major _ -> p

/// What the collection leaves to the reference side.
let mctx (rn: renaming) (w w': world) (r: rstore) (fwd: nat -> option nat) : prop =
  scorr_w rn w r /\ clean rn w r /\ rwf r /\ uc w'.maj /\
  (* visible major blocks stay, visible young ones are copied *)
  (forall (t: nat). reachable w t ==> shape_keep w.maj w'.maj t t) /\
  (forall (y: nat). yreachable w y ==> Some? (fwd y) /\ shape_keep w.yng w'.maj y (Some?.v (fwd y))) /\
  (* fields and roots forwarded *)
  (forall (p: ptr) (j: nat). visible w p /\ j < wz_of (ph w p) (pa p) ==>
     fld w' (fmu fwd p) j == fwd_field (ph w p) (pa p) j w.yng fwd) /\
  w'.roots == L.map (fwdv w.yng fwd) w.roots /\
  (* the nursery is empty *)
  (forall (y: nat). ~(is_block w'.yng y)) /\
  (* distinct blocks go to distinct places *)
  (forall (y1 y2: nat). yreachable w y1 /\ yreachable w y2 /\ fwd y1 == fwd y2 /\ Some? (fwd y1) ==> y1 == y2) /\
  (forall (t y: nat). reachable w t /\ yreachable w y ==> fwd y =!= Some t)

/// ---------------------------------------------------------------------------
/// Values
/// ---------------------------------------------------------------------------

let mc_maj (rn: renaming) (w w': world) (r: rstore) (fwd: nat -> option nat) (t: nat)
  : Lemma (requires mctx rn w w' r fwd /\ reachable w t) (ensures shape_keep w.maj w'.maj t t) = ()

let mc_yng (rn: renaming) (w w': world) (r: rstore) (fwd: nat -> option nat) (y: nat)
  : Lemma (requires mctx rn w w' r fwd /\ yreachable w y)
          (ensures Some? (fwd y) /\ shape_keep w.yng w'.maj y (Some?.v (fwd y))) = ()

/// **A forwarded value points where it pointed, moved.**
let fwd_moved (rn: renaming) (w w': world) (r: rstore) (fwd: nat -> option nat) (v: value)
  : Lemma (requires mctx rn w w' r fwd /\ (forall (q: ptr). target w v == Some q ==> visible w q))
          (ensures vmoved w w' (fmu fwd) v (fwdv w.yng fwd v))
  = match v with
    | VPtr (Major a) ->
      (match resolve w.maj a with
       | Some t ->
         mc_maj rn w w' r fwd t;
         resolve_block w.maj a t;
         resolve_move w.maj w'.maj a t t;
         assert (fwdv w.yng fwd v == v);
         assert (fmu fwd (Major t) == Major t);
         assert (ptr_at w' v (Major t) (a - t));
         vmoved_some w w' (fmu fwd) v (fwdv w.yng fwd v) (Major t) (a - t)
       | None -> ())
    | VPtr (Young b) ->
      (match resolve w.yng b with
       | Some y ->
         mc_yng rn w w' r fwd y;
         let cp = Some?.v (fwd y) in
         resolve_block w.yng b y;
         resolve_move w.yng w'.maj b y cp;
         assert (fwdv w.yng fwd v == VPtr (Major (cp + (b - y))));
         assert (fmu fwd (Young y) == Major cp);
         assert (ptr_at w' (fwdv w.yng fwd v) (Major cp) (b - y));
         vmoved_some w w' (fmu fwd) v (fwdv w.yng fwd v) (Young y) (b - y)
       | None -> ())
    | _ -> ()

/// A value with a visible target, forwarded, keeps its correspondence.
let fwd_corr (rn: renaming) (w w': world) (r: rstore) (fwd: nat -> option nat) (scan: bool) (v: value) (rv: rval)
  : Lemma (requires mctx rn w w' r fwd /\ vcorr rn w scan v rv /\
                    (RPtr? rv ==> (forall (q: ptr). target w v == Some q ==> visible w q)))
          (ensures vcorr (rn_step rn (fmu fwd) r.next None) w' scan (if scan then fwdv w.yng fwd v else v) rv)
  = match rv with
    | RPtr k d ->
      vcorr_ptr rn w scan v k d;
      fwd_moved rn w w' r fwd v;
      vcorr_move rn (fmu fwd) r.next None w w' scan v (fwdv w.yng fwd v) rv
    | RWord _ ->
      vcorr_move rn (fmu fwd) r.next None w w' scan v (if scan then fwdv w.yng fwd v else v) rv

/// ---------------------------------------------------------------------------
/// The general step's hypotheses
/// ---------------------------------------------------------------------------

let m_field (rn: renaming) (w w': world) (r: rstore) (fwd: nat -> option nat) (k: nat) (p: ptr) (j: nat)
  : Lemma (requires mctx rn w w' r fwd /\ rn k == Some p /\ j < (robj_of r k).rsz)
          (ensures vcorr (rn_step rn (fmu fwd) r.next None) w' (scannable (robj_of r k).rtag)
                         (fld w' (fmu fwd p) j) ((robj_of r k).rf j))
  = assert (visible w p);
    name_ocorr rn w r k p;
    let ro = robj_of r k in
    let scan = scannable ro.rtag in
    assert (vcorr rn w scan (fld w p j) (ro.rf j));
    assert (fld w' (fmu fwd p) j == fwd_field (ph w p) (pa p) j w.yng fwd);
    assert (tag_of (ph w p) (pa p) == ro.rtag);
    let aux (q: ptr) : Lemma (requires RPtr? (ro.rf j) /\ target w (fld w p j) == Some q) (ensures visible w q)
      = vis_field w p j q in
    C.forall_intro (C.move_requires aux);
    fwd_corr rn w w' r fwd scan (fld w p j) (ro.rf j)

let m_obj (rn: renaming) (w w': world) (r: rstore) (fwd: nat -> option nat) (k: nat)
  : Lemma (requires mctx rn w w' r fwd)
          (ensures Some? (rn k) ==> Some? (r.objs k) /\
                     ocorr (rn_step rn (fmu fwd) r.next None) w' (fmu fwd (Some?.v (rn k))) (Some?.v (r.objs k)))
  = match rn k with
    | Some p ->
      assert (visible w p);
      name_ocorr rn w r k p;
      (match p with
       | Major t -> mc_maj rn w w' r fwd t
       | Young y -> mc_yng rn w w' r fwd y);
      C.forall_intro (C.move_requires (m_field rn w w' r fwd k p))
    | None -> ()

let rec map_idx (f: value -> value) (l: list value) (j: nat)
  : Lemma (ensures L.length (L.map f l) == L.length l /\ (j < L.length l ==> L.index (L.map f l) j == f (L.index l j)))
          (decreases l)
  = match l with
    | [] -> ()
    | _ :: t -> if j = 0 then map_idx f t 0 else map_idx f t (j - 1)

let m_root (rn: renaming) (w w': world) (r: rstore) (fwd: nat -> option nat) (j: nat)
  : Lemma (requires mctx rn w w' r fwd /\ j < L.length w.roots)
          (ensures j < L.length w'.roots /\
                   vcorr (rn_step rn (fmu fwd) r.next None) w' true (L.index w'.roots j) (L.index r.rroots j))
  = map_idx (fwdv w.yng fwd) w.roots j;
    let v = L.index w.roots j in
    idx_memP w.roots j;
    C.forall_intro (C.move_requires (vis_root w v));
    fwd_corr rn w w' r fwd true v (L.index r.rroots j)

let m_inj (rn: renaming) (w w': world) (r: rstore) (fwd: nat -> option nat) (p1 p2: ptr)
  : Lemma (requires mctx rn w w' r fwd /\ visible w p1 /\ visible w p2 /\ fmu fwd p1 == fmu fwd p2)
          (ensures p1 == p2)
  = match p1, p2 with
    | Young y1, Young y2 -> mc_yng rn w w' r fwd y1; mc_yng rn w w' r fwd y2
    | Young y, Major t -> mc_yng rn w w' r fwd y
    | Major t, Young y -> mc_yng rn w w' r fwd y
    | _ -> ()

/// **The reference side of a minor collection.**
let minor_ref (rn: renaming) (w w': world) (r: rstore) (fwd: nat -> option nat)
  : Lemma (requires mctx rn w w' r fwd)
          (ensures exists (rn': renaming). scorr_w rn' w' r /\ clean rn' w' r)
  = let rn1 = rn_step rn (fmu fwd) r.next None in
    C.forall_intro (m_obj rn w w' r fwd);
    map_idx (fwdv w.yng fwd) w.roots 0;
    let f (j: nat) : Lemma (j < L.length w'.roots ==> vcorr rn1 w' true (L.index w'.roots j) (L.index r.rroots j))
      = if j < L.length w.roots then m_root rn w w' r fwd j in
    C.forall_intro f;
    assert (roots_corr rn1 w' r);
    C.forall_intro_2 (fun (p1 p2: ptr) -> C.move_requires (m_inj rn w w' r fwd p1) p2);
    assert (gen_hyps rn (fmu fwd) r.next None w w' r r);
    sim_gen rn (fmu fwd) r.next None w w' r r;
    restrict_scorr rn1 w' r
