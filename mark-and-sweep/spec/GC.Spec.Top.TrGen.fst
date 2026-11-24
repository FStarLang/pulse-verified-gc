/// ---------------------------------------------------------------------------
/// GC.Spec.Top.TrGen - one step of the correspondence, in general
/// ---------------------------------------------------------------------------
///
/// Design doc §16.15.  A step moves each visible block `p` to `mu p` (the
/// identity, or the forwarding of a minor collection) and may add one new
/// block `nw`, the store's next name `nk`.  The renaming follows
/// (`rn_step`).  If every moved block holds its object again, the new one
/// holds the new object, the roots correspond, the nursery points only into
/// the image, and `mu` is injective and misses the new block, the step keeps
/// the correspondence (`sim_gen`).  Pointers keep resolving to a block that
/// keeps its size, tag and (for a closure) its integer fields
/// (`resolve_move`).

module GC.Spec.Top.TrGen

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.Transp
open GC.Spec.Top.TrRef
open GC.Spec.Top.TrVis
module L = FStar.List.Tot
module C = FStar.Classical
module ID = FStar.IndefiniteDescription

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Pointers into a block that keeps its shape
/// ---------------------------------------------------------------------------

/// Blocks do not overlap.
let uc (h: mheap) : prop = forall (o1 o2 w: nat). covers h o1 w /\ covers h o2 w ==> o1 == o2

let uc_wf (h: mheap) : Lemma (requires well_formed h) (ensures uc h) = ()
let uc_young (h: mheap) : Lemma (requires young_ok h) (ensures uc h) = ()

/// Block `o` of `h` is block `o'` of `h'`, with its size, tag and, for a
/// closure, its integer fields (its infix headers).
let shape_keep (h h': mheap) (o o': nat) : prop =
  is_block h o /\ is_block h' o' /\ wz_of h' o' == wz_of h o /\ tag_of h' o' == tag_of h o /\
  (tag_of h o == closure_tag ==>
     (forall (j: nat). j < wz_of h o /\ VInt? (field h o j) ==> field h' o' j == field h o j))

let resolve_block (h: mheap) (a o: nat)
  : Lemma (requires resolve h a == Some o) (ensures is_block h o /\ o <= a /\ (a <> o ==> tag_of h o == closure_tag))
  = ()

#push-options "--z3rlimit 40"
/// **A pointer `o + d` to a block that moves to `o'` is `o' + d`.**
let resolve_move (h h': mheap) (a o o': nat)
  : Lemma (requires resolve h a == Some o /\ shape_keep h h' o o' /\ uc h')
          (ensures resolve h' (o' + (a - o)) == Some o')
  = if is_block h a then ()
    else begin
      let Some k = infix_hdr (h.body a) in
      assert (o == a - k /\ k >= 2 /\ k < wz_of h o);
      assert (h.body a == field h o (k - 1));
      assert (field h' o' (k - 1) == field h o (k - 1));
      assert (h'.body (o' + k) == field h' o' (k - 1));
      assert (covers h' o' (o' + k));
      if is_block h' (o' + k) then assert (covers h' (o' + k) (o' + k))
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The moved renaming
/// ---------------------------------------------------------------------------

let mapp (mu: ptr -> ptr) (q: option ptr) : option ptr = match q with Some p -> Some (mu p) | None -> None

/// After the step: the new block under the new name, the others moved.
let rn_step (rn: renaming) (mu: ptr -> ptr) (nk: nat) (nw: option ptr) : renaming =
  fun (k: nat) -> if k = nk && Some? nw then nw else mapp mu (rn k)

/// The blocks after the step: the moved visible blocks, and the new one.
let img (w: world) (mu: ptr -> ptr) (nw: option ptr) (q: ptr) : prop =
  (exists (p: ptr). visible w p /\ q == mu p) \/ nw == Some q

/// `v'`, after the step, points where `v` pointed, moved: `mu q` at the
/// same offset.
let ptr_at (w': world) (v': value) (q: ptr) (d: nat) : prop =
  match q with
  | Major o -> v' == VPtr (Major (o + d)) /\ resolve w'.maj (o + d) == Some o
  | Young o -> v' == VPtr (Young (o + d)) /\ resolve w'.yng (o + d) == Some o

/// The value `v` moved to `v'`: a word stays (and for a pointer
/// correspondence, it points to the moved target).
let vmoved (w w': world) (mu: ptr -> ptr) (v v': value) : prop =
  (VInt? v ==> v' == v) /\
  (forall (q: ptr). target w v == Some q ==>
     (exists (d: nat). ptr_at w' v' (mu q) d /\
        (match v, q with
         | VPtr (Major a), Major o -> a == o + d
         | VPtr (Young a), Young o -> a == o + d
         | _ -> False)))

let vmoved_some (w w': world) (mu: ptr -> ptr) (v v': value) (q: ptr) (d: nat)
  : Lemma (requires target w v == Some q /\ ptr_at w' v' (mu q) d /\
                    (match v, q with
                     | VPtr (Major a), Major o -> a == o + d
                     | VPtr (Young a), Young o -> a == o + d
                     | _ -> False))
          (ensures vmoved w w' mu v v')
  = ()

/// **A correspondence moves with its value.**
let vcorr_move (rn: renaming) (mu: ptr -> ptr) (nk: nat) (nw: option ptr) (w w': world) (scan: bool)
    (v v': value) (rv: rval)
  : Lemma (requires vcorr rn w scan v rv /\
                    (match rv with RWord _ -> v' == v | RPtr k _ -> vmoved w w' mu v v' /\ ~(k = nk /\ Some? nw)))
          (ensures vcorr (rn_step rn mu nk nw) w' scan v' rv)
  = match rv with
    | RWord _ -> ()
    | RPtr k d ->
      vcorr_ptr rn w scan v k d;
      let q = Some?.v (rn k) in
      eliminate exists (d': nat). ptr_at w' v' (mu q) d' /\
        (match v, q with
         | VPtr (Major a), Major o -> a == o + d'
         | VPtr (Young a), Young o -> a == o + d'
         | _ -> False)
      with assert (d' == d)

/// ---------------------------------------------------------------------------
/// The general step
/// ---------------------------------------------------------------------------

/// The name of a visible block holds its object.
let name_ocorr (rn: renaming) (w: world) (r: rstore) (k: nat) (p: ptr)
  : Lemma (requires cover rn w r /\ inj rn w /\ rn k == Some p /\ visible w p)
          (ensures Some? (r.objs k) /\ ocorr rn w p (Some?.v (r.objs k)))
  = eliminate exists (k1: nat). rn k1 == Some p /\ Some? (r.objs k1) /\ ocorr rn w p (Some?.v (r.objs k1))
    with assert (k1 == k)

/// What a step must show.
let gen_hyps (rn: renaming) (mu: ptr -> ptr) (nk: nat) (nw: option ptr) (w w': world) (r r': rstore) : prop =
  let rn' = rn_step rn mu nk nw in
  scorr_w rn w r /\ clean rn w r /\ rwf r /\ (Some? nw ==> nk == r.next) /\
  (* every visible block holds its object again, moved *)
  (forall (k: nat). {:pattern (rn k)}
     Some? (rn k) ==> Some? (r'.objs k) /\ ocorr rn' w' (mu (Some?.v (rn k))) (Some?.v (r'.objs k))) /\
  (* the new block holds the new object *)
  (Some? nw ==> Some? (r'.objs nk) /\ ocorr rn' w' (Some?.v nw) (Some?.v (r'.objs nk))) /\
  roots_corr rn' w' r' /\
  (* the nursery points only into the moved blocks *)
  (forall (y i: nat) (q: ptr). ptr_field w'.yng y i /\ target w' (field w'.yng y i) == Some q /\ Major? q ==>
     img w mu nw q) /\
  (* distinct blocks stay distinct, and none becomes the new one *)
  (forall (p1 p2: ptr). visible w p1 /\ visible w p2 /\ mu p1 == mu p2 ==> p1 == p2) /\
  (forall (p: ptr). Some? nw /\ visible w p ==> mu p =!= Some?.v nw)

let gh_obj (rn: renaming) (mu: ptr -> ptr) (nk: nat) (nw: option ptr) (w w': world) (r r': rstore) (k: nat) (p: ptr)
  : Lemma (requires gen_hyps rn mu nk nw w w' r r' /\ rn k == Some p)
          (ensures Some? (r'.objs k) /\ ocorr (rn_step rn mu nk nw) w' (mu p) (Some?.v (r'.objs k)))
  = ()

let rn_img (rn: renaming) (mu: ptr -> ptr) (nk: nat) (nw: option ptr) (w: world) (r: rstore) (k: nat) (q: ptr)
  : Lemma (requires clean rn w r /\ rn_step rn mu nk nw k == Some q) (ensures img w mu nw q)
  = if k = nk && Some? nw then () else assert (visible w (Some?.v (rn k)))

/// The name of a block of the image.
let img_name (rn: renaming) (mu: ptr -> ptr) (nk: nat) (nw: option ptr) (w w': world) (r r': rstore) (q: ptr)
  : Lemma (requires gen_hyps rn mu nk nw w w' r r' /\ img w mu nw q)
          (ensures exists (k: nat). rn_step rn mu nk nw k == Some q /\ Some? (r'.objs k) /\
                                    ocorr (rn_step rn mu nk nw) w' q (Some?.v (r'.objs k)))
  = if ID.strong_excluded_middle (nw == Some q) then ()
    else
      eliminate exists (p: ptr). visible w p /\ q == mu p
      with eliminate exists (k: nat). rn k == Some p /\ Some? (r.objs k) /\ ocorr rn w p (Some?.v (r.objs k))
           with begin
             assert (k < r.next);
             assert (rn_step rn mu nk nw k == Some (mu p));
             gh_obj rn mu nk nw w w' r r' k p
           end

let img_field (rn: renaming) (mu: ptr -> ptr) (nk: nat) (nw: option ptr) (w w': world) (r r': rstore)
    (q: ptr) (i: nat) (q': ptr)
  : Lemma (requires gen_hyps rn mu nk nw w w' r r' /\ img w mu nw q /\ pfield w' q i /\ target w' (fld w' q i) == Some q')
          (ensures img w mu nw q')
  = let rn' = rn_step rn mu nk nw in
    img_name rn mu nk nw w w' r r' q;
    eliminate exists (k: nat). rn' k == Some q /\ Some? (r'.objs k) /\ ocorr rn' w' q (Some?.v (r'.objs k))
    with begin
      let ro = Some?.v (r'.objs k) in
      assert (vcorr rn' w' (scannable ro.rtag) (fld w' q i) (ro.rf i));
      match ro.rf i with
      | RPtr k' d -> vcorr_ptr rn' w' (scannable ro.rtag) (fld w' q i) k' d; rn_img rn mu nk nw w r k' q'
      | RWord _ -> ()
    end

let img_root (rn: renaming) (mu: ptr -> ptr) (nk: nat) (nw: option ptr) (w w': world) (r r': rstore)
    (v: value) (q: ptr)
  : Lemma (requires gen_hyps rn mu nk nw w w' r r' /\ L.memP v w'.roots /\ target w' v == Some q)
          (ensures img w mu nw q)
  = let rn' = rn_step rn mu nk nw in
    memP_idx v w'.roots;
    eliminate exists (j: nat). j < L.length w'.roots /\ L.index w'.roots j == v
    with begin
      assert (vcorr rn' w' true v (L.index r'.rroots j));
      match L.index r'.rroots j with
      | RPtr k' d -> vcorr_ptr rn' w' true v k' d; rn_img rn mu nk nw w r k' q
      | RWord _ -> ()
    end

let img_closed (rn: renaming) (mu: ptr -> ptr) (nk: nat) (nw: option ptr) (w w': world) (r r': rstore)
  : Lemma (requires gen_hyps rn mu nk nw w w' r r') (ensures vclosed w' (img w mu nw))
  = C.forall_intro_2 (fun (v: value) (q: ptr) -> C.move_requires (img_root rn mu nk nw w w' r r' v) q);
    let f (q: ptr) (i: nat) (q': ptr)
      : Lemma (img w mu nw q /\ pfield w' q i /\ target w' (fld w' q i) == Some q' ==> img w mu nw q')
      = C.move_requires (img_field rn mu nk nw w w' r r' q i) q' in
    C.forall_intro_3 f

let gen_inj (rn: renaming) (mu: ptr -> ptr) (nk: nat) (nw: option ptr) (w w': world) (r r': rstore)
    (k1 k2: nat) (q: ptr)
  : Lemma (requires gen_hyps rn mu nk nw w w' r r' /\ rn_step rn mu nk nw k1 == Some q /\
                    rn_step rn mu nk nw k2 == Some q)
          (ensures k1 == k2)
  = let new1 = k1 = nk && Some? nw in
    let new2 = k2 = nk && Some? nw in
    if new1 && new2 then ()
    else if new1 then assert (visible w (Some?.v (rn k2)))
    else if new2 then assert (visible w (Some?.v (rn k1)))
    else begin
      let p1 = Some?.v (rn k1) in
      let p2 = Some?.v (rn k2) in
      assert (visible w p1 /\ visible w p2);
      assert (p1 == p2)
    end

/// **The general step.**
let sim_gen (rn: renaming) (mu: ptr -> ptr) (nk: nat) (nw: option ptr) (w w': world) (r r': rstore)
  : Lemma (requires gen_hyps rn mu nk nw w w' r r')
          (ensures scorr_w (rn_step rn mu nk nw) w' r')
  = let rn' = rn_step rn mu nk nw in
    img_closed rn mu nk nw w w' r r';
    vis_sub w' (img w mu nw);
    C.forall_intro (C.move_requires (img_name rn mu nk nw w w' r r'));
    C.forall_intro_3 (fun (k1 k2: nat) (q: ptr) -> C.move_requires (gen_inj rn mu nk nw w w' r r' k1 k2) q);
    scorr_intro rn' w' r'
