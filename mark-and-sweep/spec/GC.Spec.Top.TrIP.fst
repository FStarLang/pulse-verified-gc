/// ---------------------------------------------------------------------------
/// GC.Spec.Top.TrIP - steps that leave every visible block in place
/// ---------------------------------------------------------------------------
///
/// Design doc §16.15.  Every step but a minor collection keeps each visible
/// block where it is, with its size, tag and (for a closure) its integer
/// fields (`ip_ctx`).  A field it does not change keeps its correspondence
/// (`field_keep`), so a block whose fields are unchanged or shown to
/// correspond holds its object again (`ocorr_keep`).  A value the program
/// passes in is named on the reference side (`trv`).

module GC.Spec.Top.TrIP

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

let pid (p: ptr) : ptr = p

let ip_ctx (rn: renaming) (w w': world) (r: rstore) : prop =
  scorr_w rn w r /\ clean rn w r /\ rwf r /\ uc w'.maj /\ uc w'.yng /\
  (forall (q: ptr). visible w q ==> shape_keep (ph w q) (ph w' q) (pa q) (pa q))

let ip_keep (rn: renaming) (w w': world) (r: rstore) (q: ptr)
  : Lemma (requires ip_ctx rn w w' r /\ visible w q) (ensures shape_keep (ph w q) (ph w' q) (pa q) (pa q))
  = ()

/// A value pointing to a visible block points to it after the step.
let vmoved_id (rn: renaming) (w w': world) (r: rstore) (v: value)
  : Lemma (requires ip_ctx rn w w' r /\ (forall (q: ptr). target w v == Some q ==> visible w q))
          (ensures vmoved w w' pid v v)
  = match v with
    | VPtr (Major a) ->
      (match resolve w.maj a with
       | Some o ->
         ip_keep rn w w' r (Major o);
         resolve_block w.maj a o;
         resolve_move w.maj w'.maj a o o;
         assert (ptr_at w' v (Major o) (a - o));
         vmoved_some w w' pid v v (Major o) (a - o)
       | None -> ())
    | VPtr (Young a) ->
      (match resolve w.yng a with
       | Some o ->
         ip_keep rn w w' r (Young o);
         resolve_block w.yng a o;
         resolve_move w.yng w'.yng a o o;
         assert (ptr_at w' v (Young o) (a - o));
         vmoved_some w w' pid v v (Young o) (a - o)
       | None -> ())
    | _ -> ()

/// A major pointer to a visible block points to it after the step.
let maj_target (rn: renaming) (w w': world) (r: rstore) (nw: option ptr) (u: value) (q: ptr)
  : Lemma (requires ip_ctx rn w w' r /\ VPtr? u /\ Major? (VPtr?._0 u) /\
                    (forall (q0: ptr). target w u == Some q0 ==> visible w q0) /\
                    Some? (target w u) /\ target w' u == Some q)
          (ensures img w pid nw q)
  = vmoved_id rn w w' r u;
    let VPtr (Major a) = u in
    let Some o' = resolve w.maj a in
    assert (visible w (Major o'));
    ip_keep rn w w' r (Major o');
    resolve_block w.maj a o';
    resolve_move w.maj w'.maj a o' o';
    assert (o' + (a - o') == a);
    assert (resolve w'.maj a == Some o');
    assert (q == Major o')

/// **A field the step does not change keeps its correspondence.**
let field_keep (rn: renaming) (nk: nat) (nw: option ptr) (w w': world) (r: rstore) (k: nat) (p: ptr) (i: nat)
  : Lemma (requires ip_ctx rn w w' r /\ (Some? nw ==> nk == r.next) /\ rn k == Some p /\
                    i < (robj_of r k).rsz /\ fld w' p i == fld w p i)
          (ensures vcorr (rn_step rn pid nk nw) w' (scannable (robj_of r k).rtag) (fld w' p i) ((robj_of r k).rf i))
  = assert (visible w p);
    name_ocorr rn w r k p;
    let ro = robj_of r k in
    let scan = scannable ro.rtag in
    assert (vcorr rn w scan (fld w p i) (ro.rf i));
    match ro.rf i with
    | RPtr k' d ->
      vcorr_ptr rn w scan (fld w p i) k' d;
      let q = Some?.v (rn k') in
      vis_field w p i q;
      name_ok rn w r k' q;
      vmoved_id rn w w' r (fld w p i);
      vcorr_move rn pid nk nw w w' scan (fld w p i) (fld w' p i) (ro.rf i)
    | RWord _ -> vcorr_move rn pid nk nw w w' scan (fld w p i) (fld w' p i) (ro.rf i)

/// **A block holds its object again** when each field is unchanged or
/// corresponds.
let ocorr_keep (rn: renaming) (nk: nat) (nw: option ptr) (w w': world) (r: rstore) (k: nat) (p: ptr) (ro': robj)
  : Lemma (requires ip_ctx rn w w' r /\ (Some? nw ==> nk == r.next) /\ rn k == Some p /\
                    ro'.rtag == (robj_of r k).rtag /\ ro'.rsz == (robj_of r k).rsz /\
                    (forall (i: nat). i < ro'.rsz ==>
                       (fld w' p i == fld w p i /\ ro'.rf i == (robj_of r k).rf i) \/
                       vcorr (rn_step rn pid nk nw) w' (scannable ro'.rtag) (fld w' p i) (ro'.rf i)))
          (ensures ocorr (rn_step rn pid nk nw) w' p ro')
  = assert (visible w p);
    name_ocorr rn w r k p;
    ip_keep rn w w' r p;
    let f (i: nat) : Lemma (i < ro'.rsz ==> vcorr (rn_step rn pid nk nw) w' (scannable ro'.rtag) (fld w' p i) (ro'.rf i))
      = if i < ro'.rsz && ID.strong_excluded_middle (fld w' p i == fld w p i /\ ro'.rf i == (robj_of r k).rf i)
        then field_keep rn nk nw w w' r k p i in
    C.forall_intro f

/// ---------------------------------------------------------------------------
/// Naming the program's values
/// ---------------------------------------------------------------------------

let named (rn: renaming) (r: rstore) (q: ptr) (k: nat) : prop = rn k == Some q /\ Some? (r.objs k)

let name_of (rn: renaming) (r: rstore) (q: ptr) : GTot nat =
  if ID.strong_excluded_middle (exists (k: nat). named rn r q k)
  then ID.indefinite_description_ghost nat (fun k -> named rn r q k)
  else 0

/// The reference value of a program value: a pointer by its target's name
/// and offset, any other word as it is.
let trv (rn: renaming) (w: world) (r: rstore) (scan: bool) (v: value) : GTot rval =
  if scan then
    (match v, target w v with
     | VPtr (Major a), Some q -> RPtr (name_of rn r q) (a - pa q)
     | VPtr (Young a), Some q -> RPtr (name_of rn r q) (a - pa q)
     | _ -> RWord v)
  else RWord v

let trv_ok (rn: renaming) (w: world) (r: rstore) (scan: bool) (v: value)
  : Lemma (requires scorr_w rn w r /\ rwf r /\ (scan ==> value_ok w v))
          (ensures vcorr rn w scan v (trv rn w r scan v) /\ rval_ok r scan (trv rn w r scan v) /\
                   (match trv rn w r scan v with
                    | RPtr k _ -> (exists (q: ptr). rn k == Some q /\ visible w q) /\ k < r.next
                    | _ -> True))
  = if scan then
      match v with
      | VPtr (Major a) ->
        let Some o = resolve w.maj a in
        resolve_block w.maj a o;
        let q = Major o in
        assert (visible w q);
        assert (exists (k: nat). named rn r q k);
        let k = name_of rn r q in
        assert (named rn r q k)
      | VPtr (Young a) ->
        let Some o = resolve w.yng a in
        resolve_block w.yng a o;
        let q = Young o in
        assert (visible w q);
        assert (exists (k: nat). named rn r q k);
        let k = name_of rn r q in
        assert (named rn r q k)
      | _ -> ()

/// The heads of corresponding roots correspond.
let head_corr (rn: renaming) (w: world) (r: rstore)
  : Lemma (requires roots_corr rn w r)
          (ensures vcorr rn w true (head_or (VInt 0) w.roots) (head_or (RWord (VInt 0)) r.rroots))
  = match w.roots with
    | [] -> ()
    | _ :: _ -> assert (vcorr rn w true (L.index w.roots 0) (L.index r.rroots 0))
