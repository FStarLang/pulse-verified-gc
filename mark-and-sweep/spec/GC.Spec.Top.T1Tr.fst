/// ---------------------------------------------------------------------------
/// GC.Spec.Top.T1Tr - T1, part 2: a reference event, run on another world
/// ---------------------------------------------------------------------------
///
/// Design doc §16.18.  The replay performs the program's next reference
/// event on its own world, through its own renaming.  A reference value is
/// a word as it is, or the renamed block's address plus the offset (`tv`).
/// Where the original run performed the event (`wit`), the translation is
/// legal: the program's obligations hold of it and it is the reference
/// event, renamed (`tev_exists`).  A pointer's offset stays good because
/// both blocks hold the same reference object, so have the same shape
/// (`ocorr_shape`).  The renamed event determines the reference event
/// (`ev_unique`), and a renamed list of values is unique (`vlist_unique`).

module GC.Spec.Top.T1Tr

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Transp
open GC.Spec.Top.TrRef
open GC.Spec.Top.TrVis
open GC.Spec.Top.TrGen
open GC.Spec.Top.T1Re
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module C = FStar.Classical
module ID = FStar.IndefiniteDescription

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Values
/// ---------------------------------------------------------------------------

let mkp (p: ptr) (d: nat) : value =
  match p with Major o -> VPtr (Major (o + d)) | Young o -> VPtr (Young (o + d))

let tv (rn: renaming) (rv: rval) : value =
  match rv with
  | RWord u -> u
  | RPtr k d -> (match rn k with Some p -> mkp p d | None -> VInt 0)

let rec tvs (rn: renaming) (l: list rval) : list value =
  match l with [] -> [] | h :: t -> tv rn h :: tvs rn t

let rec tvs_len (rn: renaming) (l: list rval) : Lemma (L.length (tvs rn l) == L.length l)
  = match l with [] -> () | _ :: t -> tvs_len rn t

let rec tvs_idx (rn: renaming) (l: list rval) (i: nat)
  : Lemma (requires i < L.length l)
          (ensures i < L.length (tvs rn l) /\ L.index (tvs rn l) i == tv rn (L.index l i)) (decreases l)
  = tvs_len rn l;
    match l with _ :: t -> if i = 0 then () else tvs_idx rn t (i - 1)

/// A renamed value is unique.
let tv_unique (rn: renaming) (w: world) (scan: bool) (v: value) (rv: rval)
  : Lemma (requires vcorr rn w scan v rv) (ensures v == tv rn rv)
  = match rv with
    | RWord _ -> ()
    | RPtr k d ->
      (match v with
       | VPtr (Major a) -> eliminate exists (o: nat). rn k == Some (Major o) /\ a == o + d /\ resolve w.maj a == Some o
                           with ()
       | VPtr (Young a) -> eliminate exists (o: nat). rn k == Some (Young o) /\ a == o + d /\ resolve w.yng a == Some o
                           with ())

let vlist_unique (rn: renaming) (w: world) (scan: bool) (vs1 vs2: list value) (rvs: list rval)
  : Lemma (requires vcorr_list rn w scan vs1 rvs /\ vcorr_list rn w scan vs2 rvs) (ensures vs1 == vs2)
  = let f (i: nat) : Lemma (i < L.length vs1 ==> L.index vs1 i == L.index vs2 i)
      = if i < L.length vs1 then begin
          tv_unique rn w scan (L.index vs1 i) (L.index rvs i);
          tv_unique rn w scan (L.index vs2 i) (L.index rvs i)
        end in
    C.forall_intro f;
    LP.index_extensionality vs1 vs2

/// A value names one reference value.
let rv_unique (rn: renaming) (w: world) (r: rstore) (scan: bool) (v: value) (rv1 rv2: rval)
  : Lemma (requires clean rn w r /\ inj rn w /\ vcorr rn w scan v rv1 /\ vcorr rn w scan v rv2)
          (ensures rv1 == rv2)
  = match rv1, rv2 with
    | RPtr k1 d1, RPtr k2 d2 ->
      vcorr_ptr rn w scan v k1 d1;
      vcorr_ptr rn w scan v k2 d2;
      let Some p = rn k1 in
      assert (visible w p);
      assert (k1 == k2);
      tv_unique rn w scan v rv1;
      tv_unique rn w scan v rv2
    | _ -> ()

let rvs_unique (rn: renaming) (w: world) (r: rstore) (scan: bool) (vs: list value) (rvs1 rvs2: list rval)
  : Lemma (requires clean rn w r /\ inj rn w /\ vcorr_list rn w scan vs rvs1 /\ vcorr_list rn w scan vs rvs2)
          (ensures rvs1 == rvs2)
  = let f (i: nat) : Lemma (i < L.length rvs1 ==> L.index rvs1 i == L.index rvs2 i)
      = if i < L.length rvs1 then rv_unique rn w r scan (L.index vs i) (L.index rvs1 i) (L.index rvs2 i) in
    C.forall_intro f;
    LP.index_extensionality rvs1 rvs2

/// **A renamed event names one reference event.**
let ev_unique (rn: renaming) (w: world) (r: rstore) (e: event) (re1 re2: revent)
  : Lemma (requires clean rn w r /\ inj rn w /\ ev_corr rn w r e re1 /\ ev_corr rn w r e re2)
          (ensures re1 == re2)
  = match e, re1, re2 with
    | EAlloc _ tag vs, RAlloc _ _ rvs1, RAlloc _ _ rvs2 -> rvs_unique rn w r (scannable tag) vs rvs1 rvs2
    | EYoungAlloc _ tag vs, RAlloc _ _ rvs1, RAlloc _ _ rvs2 -> rvs_unique rn w r (scannable tag) vs rvs1 rvs2
    | EWrite p _ v, RWrite k1 _ rv1, RWrite k2 _ rv2 ->
      assert (visible w p);
      assert (k1 == k2);
      rv_unique rn w r (scannable (robj_of r k1).rtag) v rv1 rv2
    | ERead p _, RRead k1 _, RRead k2 _ -> assert (visible w p); assert (k1 == k2)
    | ERoots vs, RRoots rvs1, RRoots rvs2 -> rvs_unique rn w r true vs rvs1 rvs2
    | _ -> ()

/// ---------------------------------------------------------------------------
/// Blocks holding one object have one shape
/// ---------------------------------------------------------------------------

let ocorr_ph (rn: renaming) (w: world) (p: ptr) (ro: robj)
  : Lemma (ocorr rn w p ro <==>
           (is_block (ph w p) (pa p) /\ tag_of (ph w p) (pa p) == ro.rtag /\ wz_of (ph w p) (pa p) == ro.rsz /\
            (forall (i: nat). i < ro.rsz ==> vcorr rn w (scannable ro.rtag) (fld w p i) (ro.rf i))))
  = ()

let ocorr_shape (rn0: renaming) (w0: world) (p0: ptr) (rn: renaming) (w: world) (p: ptr) (ro: robj)
  : Lemma (requires ocorr rn0 w0 p0 ro /\ ocorr rn w p ro)
          (ensures shape_keep (ph w0 p0) (ph w p) (pa p0) (pa p))
  = ocorr_ph rn0 w0 p0 ro;
    ocorr_ph rn w p ro;
    let f (j: nat) : Lemma (j < ro.rsz /\ VInt? (fld w0 p0 j) ==> fld w p j == fld w0 p0 j)
      = if j < ro.rsz then begin
          assert (vcorr rn0 w0 (scannable ro.rtag) (fld w0 p0 j) (ro.rf j));
          assert (vcorr rn w (scannable ro.rtag) (fld w p j) (ro.rf j))
        end in
    C.forall_intro f

/// ---------------------------------------------------------------------------
/// A translated value
/// ---------------------------------------------------------------------------

/// The original world, where the event was performed.
let src (rn0: renaming) (w0: world) (r: rstore) : prop = scorr_w rn0 w0 r /\ clean rn0 w0 r

/// The replay's world.
let dst (rn: renaming) (w: world) (r: rstore) : prop =
  scorr_w rn w r /\ clean rn w r /\ uc w.maj /\ uc w.yng /\ rpos r

/// Its heaps' bounds, for the words it can hold.
let wbound (#t #yt: Type0) (rp: rep t yt) (w: world) : prop =
  rich rp /\ rp.size_ok w.maj.size /\ rp.ysize_ok w.yng.size /\ well_formed w.maj /\ young_ok w.yng

let ph_uc (w: world) (p: ptr) : Lemma (requires uc w.maj /\ uc w.yng) (ensures uc (ph w p)) = ()

let src_ptr (rn0: renaming) (w0: world) (scan: bool) (v0: value) (k d: nat)
  : Lemma (requires vcorr rn0 w0 scan v0 (RPtr k d))
          (ensures (let p0 = Some?.v (rn0 k) in
                    Some? (rn0 k) /\ VPtr? v0 /\ pa (VPtr?._0 v0) == pa p0 + d /\
                    resolve (ph w0 p0) (pa (VPtr?._0 v0)) == Some (pa p0)))
  = match v0 with
    | VPtr (Major a) -> eliminate exists (o: nat). rn0 k == Some (Major o) /\ a == o + d /\ resolve w0.maj a == Some o
                        with ()
    | VPtr (Young a) -> eliminate exists (o: nat). rn0 k == Some (Young o) /\ a == o + d /\ resolve w0.yng a == Some o
                        with ()

let dst_ptr (rn: renaming) (w: world) (scan: bool) (k d: nat) (p: ptr)
  : Lemma (requires scan /\ rn k == Some p /\ resolve (ph w p) (pa p + d) == Some (pa p))
          (ensures tv rn (RPtr k d) == mkp p d /\ vcorr rn w scan (mkp p d) (RPtr k d))
  = ()

/// **A pointer to a reachable object translates.**
let tv_ptr (rn0: renaming) (w0: world) (rn: renaming) (w: world) (r: rstore) (scan: bool) (v0: value) (k d: nat)
  : Lemma (requires src rn0 w0 r /\ dst rn w r /\ vcorr rn0 w0 scan v0 (RPtr k d) /\ rreachable r k)
          (ensures exists (p: ptr). rn k == Some p /\ visible w p /\ tv rn (RPtr k d) == mkp p d /\
                     vcorr rn w scan (mkp p d) (RPtr k d) /\
                     resolve (ph w p) (pa p + d) == Some (pa p) /\ wz_of (ph w p) (pa p) >= 1)
  = src_ptr rn0 w0 scan v0 k d;
    let p0 = Some?.v (rn0 k) in
    let a0 = pa (VPtr?._0 v0) in
    assert (visible w0 p0);
    eliminate exists (p: ptr). rn k == Some p /\ visible w p
    with begin
      name_ocorr rn0 w0 r k p0;
      name_ocorr rn w r k p;
      let ro = Some?.v (r.objs k) in
      ocorr_shape rn0 w0 p0 rn w p ro;
      ocorr_ph rn w p ro;
      ph_uc w p;
      resolve_move (ph w0 p0) (ph w p) a0 (pa p0) (pa p);
      assert (a0 - pa p0 == d);
      dst_ptr rn w scan k d p
    end

let resolve_lt (h: mheap) (a o: nat)
  : Lemma (requires resolve h a == Some o /\ wz_of h o >= 1) (ensures a < o + wz_of h o)
  = ()

let mkp_storable (#t #yt: Type0) (rp: rep t yt) (w: world) (p: ptr) (d: nat)
  : Lemma (requires wbound rp w /\ resolve (ph w p) (pa p + d) == Some (pa p) /\ wz_of (ph w p) (pa p) >= 1)
          (ensures rp.storable (mkp p d))
  = resolve_lt (ph w p) (pa p + d) (pa p);
    resolve_block (ph w p) (pa p + d) (pa p)

let mkp_ok (w: world) (p: ptr) (d: nat)
  : Lemma (requires visible w p /\ resolve (ph w p) (pa p + d) == Some (pa p)) (ensures value_ok w (mkp p d))
  = ()

/// **A value of the event translates**: it is the reference value,
/// renamed, the program may hold it, and a field can hold it.
let tv_full (#t #yt: Type0) (rp: rep t yt) (rn0: renaming) (w0: world) (rn: renaming) (w: world) (r: rstore)
    (scan: bool) (v0: value) (rv: rval)
  : Lemma (requires src rn0 w0 r /\ dst rn w r /\ wbound rp w /\ vcorr rn0 w0 scan v0 rv /\ rp.storable v0 /\
                    rval_ok r scan rv /\ rval_reach r rv)
          (ensures vcorr rn w scan (tv rn rv) rv /\ (scan ==> value_ok w (tv rn rv)) /\ rp.storable (tv rn rv))
  = match rv with
    | RWord u -> ()
    | RPtr k d ->
      tv_ptr rn0 w0 rn w r scan v0 k d;
      eliminate exists (p: ptr). rn k == Some p /\ visible w p /\ tv rn (RPtr k d) == mkp p d /\
                     vcorr rn w scan (mkp p d) (RPtr k d) /\
                     resolve (ph w p) (pa p + d) == Some (pa p) /\ wz_of (ph w p) (pa p) >= 1
      with begin
        mkp_storable rp w p d;
        mkp_ok w p d
      end

/// The same, for a list.
let tvs_full (#t #yt: Type0) (rp: rep t yt) (rn0: renaming) (w0: world) (rn: renaming) (w: world) (r: rstore)
    (scan: bool) (vs0: list value) (rvs: list rval)
  : Lemma (requires src rn0 w0 r /\ dst rn w r /\ wbound rp w /\ vcorr_list rn0 w0 scan vs0 rvs /\
                    storable_all rp vs0 /\
                    (forall (i: nat). i < L.length rvs ==> rval_ok r scan (L.index rvs i) /\ rval_reach r (L.index rvs i)))
          (ensures vcorr_list rn w scan (tvs rn rvs) rvs /\ storable_all rp (tvs rn rvs) /\
                   (forall (i: nat). i < L.length (tvs rn rvs) ==> (scan ==> value_ok w (L.index (tvs rn rvs) i))) /\
                   (forall (v: value). L.memP v (tvs rn rvs) ==> (scan ==> value_ok w v)))
  = let vs = tvs rn rvs in
    tvs_len rn rvs;
    let f (i: nat) : Lemma (i < L.length vs ==>
                            vcorr rn w scan (L.index vs i) (L.index rvs i) /\ (scan ==> value_ok w (L.index vs i)) /\
                            rp.storable (L.index vs i))
      = if i < L.length vs then begin
          tvs_idx rn rvs i;
          idx_memP vs0 i;
          tv_full rp rn0 w0 rn w r scan (L.index vs0 i) (L.index rvs i)
        end in
    C.forall_intro f;
    let g (v: value) : Lemma (L.memP v vs ==> rp.storable v /\ (scan ==> value_ok w v))
      = if ID.strong_excluded_middle (L.memP v vs) then memP_idx v vs in
    C.forall_intro g

/// ---------------------------------------------------------------------------
/// A translated event
/// ---------------------------------------------------------------------------

let pget (q: option ptr) : ptr = match q with Some p -> p | None -> Major 0

/// The event the replay performs for `re`, where the original run performed
/// `e0` (its size and tag are kept).
let tev (rn: renaming) (e0: event) (re: revent) : event =
  match e0, re with
  | EAlloc sz tag _, RAlloc _ _ rvs -> EAlloc sz tag (tvs rn rvs)
  | EYoungAlloc sz tag _, RAlloc _ _ rvs -> EYoungAlloc sz tag (tvs rn rvs)
  | EWrite _ i _, RWrite k _ rv -> EWrite (pget (rn k)) i (tv rn rv)
  | ERead _ i, RRead k _ -> ERead (pget (rn k)) i
  | ERoots _, RRoots rvs -> ERoots (tvs rn rvs)
  | _ -> e0

let hyp (#t #yt: Type0) (rp: rep t yt) (rn0: renaming) (w0: world) (rn: renaming) (w: world) (r: rstore) : prop =
  src rn0 w0 r /\ dst rn w r /\ wbound rp w

let alloc_idx (r: rstore) (tag: tag_t) (rvs: list rval)
  : Lemma (requires rok r (RAlloc true tag rvs) /\ names_reach r (RAlloc true tag rvs))
          (ensures forall (i: nat). i < L.length rvs ==> rval_ok r (scannable tag) (L.index rvs i) /\ rval_reach r (L.index rvs i))
  = ()

let tev_alloc (c: comps) (rn0: renaming) (w0: world) (rn: renaming) (w: world) (r: rstore) (e0: event) (re: revent)
  : Lemma (requires hyp c.r rn0 w0 rn w r /\ (EAlloc? e0 \/ EYoungAlloc? e0) /\
                    ev_corr rn0 w0 r e0 re /\ mutator_ok_w c w0 e0 /\ rok r re /\ names_reach r re)
          (ensures ev_corr rn w r (tev rn e0 re) re /\ mutator_ok_w c w (tev rn e0 re))
  = match e0, re with
    | EAlloc sz tag vs0, RAlloc y _ rvs ->
      alloc_idx r tag rvs;
      tvs_full c.r rn0 w0 rn w r (scannable tag) vs0 rvs
    | EYoungAlloc sz tag vs0, RAlloc y _ rvs ->
      alloc_idx r tag rvs;
      tvs_full c.r rn0 w0 rn w r (scannable tag) vs0 rvs

let tev_write (c: comps) (rn0: renaming) (w0: world) (rn: renaming) (w: world) (r: rstore) (e0: event) (re: revent)
  : Lemma (requires hyp c.r rn0 w0 rn w r /\ EWrite? e0 /\
                    ev_corr rn0 w0 r e0 re /\ mutator_ok_w c w0 e0 /\ rok r re /\ names_reach r re)
          (ensures ev_corr rn w r (tev rn e0 re) re /\ mutator_ok_w c w (tev rn e0 re))
  = match e0, re with
    | EWrite p0 i v0, RWrite k _ rv ->
      assert (c.r.storable v0);
      eliminate exists (p: ptr). rn k == Some p /\ visible w p
      with begin
        name_ocorr rn w r k p;
        let ro = Some?.v (r.objs k) in
        ocorr_ph rn w p ro;
        tv_full c.r rn0 w0 rn w r (scannable ro.rtag) v0 rv
      end

let tev_read (c: comps) (rn0: renaming) (w0: world) (rn: renaming) (w: world) (r: rstore) (e0: event) (re: revent)
  : Lemma (requires hyp c.r rn0 w0 rn w r /\ ERead? e0 /\
                    ev_corr rn0 w0 r e0 re /\ mutator_ok_w c w0 e0 /\ rok r re /\ names_reach r re)
          (ensures ev_corr rn w r (tev rn e0 re) re /\ mutator_ok_w c w (tev rn e0 re))
  = match e0, re with
    | ERead p0 i, RRead k _ ->
      eliminate exists (p: ptr). rn k == Some p /\ visible w p
      with begin
        name_ocorr rn w r k p;
        ocorr_ph rn w p (Some?.v (r.objs k))
      end

let tev_roots (c: comps) (rn0: renaming) (w0: world) (rn: renaming) (w: world) (r: rstore) (e0: event) (re: revent)
  : Lemma (requires hyp c.r rn0 w0 rn w r /\ ERoots? e0 /\
                    ev_corr rn0 w0 r e0 re /\ mutator_ok_w c w0 e0 /\ rok r re /\ names_reach r re)
          (ensures ev_corr rn w r (tev rn e0 re) re /\ mutator_ok_w c w (tev rn e0 re))
  = match e0, re with
    | ERoots vs0, RRoots rvs ->
      let f (i: nat) : Lemma (i < L.length rvs ==> rval_ok r true (L.index rvs i) /\ rval_reach r (L.index rvs i))
        = if i < L.length rvs then idx_memP rvs i in
      C.forall_intro f;
      tvs_full c.r rn0 w0 rn w r true vs0 rvs

/// The original run performed `re` somewhere.
let wit (c: comps) (r: rstore) (re: revent) : prop =
  exists (rn0: renaming) (w0: world) (e0: event). src rn0 w0 r /\ ev_corr rn0 w0 r e0 re /\ mutator_ok_w c w0 e0

/// **The replay can perform the reference event.**
let tev_exists (c: comps) (rn: renaming) (w: world) (r: rstore) (re: revent)
  : Lemma (requires wit c r re /\ dst rn w r /\ wbound c.r w /\ rok r re /\ names_reach r re)
          (ensures exists (e: event). is_mutator_event e /\ ev_corr rn w r e re /\ mutator_ok_w c w e)
  = eliminate exists (rn0: renaming) (w0: world) (e0: event). src rn0 w0 r /\ ev_corr rn0 w0 r e0 re /\ mutator_ok_w c w0 e0
    with begin
      (match e0 with
       | EAlloc _ _ _ | EYoungAlloc _ _ _ -> tev_alloc c rn0 w0 rn w r e0 re
       | EWrite _ _ _ -> tev_write c rn0 w0 rn w r e0 re
       | ERead _ _ -> tev_read c rn0 w0 rn w r e0 re
       | ERoots _ -> tev_roots c rn0 w0 rn w r e0 re
       | _ -> ());
      assert (is_mutator_event (tev rn e0 re))
    end
