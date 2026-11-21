/// ---------------------------------------------------------------------------
/// GC.Spec.Top.IdRep - the model as its own representation
/// ---------------------------------------------------------------------------
///
/// When the components work on the model heap itself and the representation
/// relation is equality (`is_id`), a lifted contract is the model contract
/// at the heap: `lifted r pre h h' post <==> (pre h ==> post h h')`, and
/// likewise for the other lifting forms.  The toy instance
/// (GC.Spec.Top.Toy*) is proved, and the broken components
/// (GC.Spec.Top.Broken) rejected, through these.

module GC.Spec.Top.IdRep

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
module L = FStar.List.Tot

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

[@@"opaque_to_smt"]
let is_id (r: rep mheap mheap) : prop =
  (forall (m h: mheap). r.repr m h <==> m == h) /\
  (forall (m y: mheap). r.yrepr m y <==> m == y)

let id_repr (r: rep mheap mheap) (m h: mheap)
  : Lemma (requires is_id r) (ensures r.repr m h <==> m == h)
  = reveal_opaque (`%is_id) (is_id r)

let id_yrepr (r: rep mheap mheap) (m y: mheap)
  : Lemma (requires is_id r) (ensures r.yrepr m y <==> m == y)
  = reveal_opaque (`%is_id) (is_id r)

let forall_repr_id (r: rep mheap mheap) (h: mheap) (f: mheap -> prop)
  : Lemma (requires is_id r) (ensures forall_repr r h f <==> f h)
  = id_repr r h h;
    let d (_: squash (f h)) (m: mheap) : Lemma (r.repr m h ==> f m) = id_repr r m h in
    FStar.Classical.impl_intro_gen #(f h) #(fun _ -> forall_repr r h f) (fun q -> FStar.Classical.forall_intro (d q))

let forall_repr2_id (r: rep mheap mheap) (h h': mheap) (f: mheap -> mheap -> prop)
  : Lemma (requires is_id r) (ensures forall_repr2 r h h' f <==> f h h')
  = id_repr r h h; id_repr r h' h';
    let d (_: squash (f h h')) (m m': mheap) : Lemma (r.repr m h /\ r.repr m' h' ==> f m m')
      = id_repr r m h; id_repr r m' h' in
    FStar.Classical.impl_intro_gen #(f h h') #(fun _ -> forall_repr2 r h h' f)
      (fun q -> FStar.Classical.forall_intro_2 (d q))

let lifted_id (r: rep mheap mheap) (pre: mheap -> prop) (h h': mheap) (post: mheap -> mheap -> prop)
  : Lemma (requires is_id r) (ensures lifted r pre h h' post <==> (pre h ==> post h h'))
  = id_repr r h h; id_repr r h' h';
    let d (_: squash (pre h ==> post h h')) (m: mheap)
      : Lemma (r.repr m h /\ pre m ==> (exists (m': mheap). r.repr m' h' /\ post m m'))
      = id_repr r m h in
    FStar.Classical.impl_intro_gen #(pre h ==> post h h') #(fun _ -> lifted r pre h h' post)
      (fun q -> FStar.Classical.forall_intro (d q));
    let e (_: squash (lifted r pre h h' post)) (_: squash (pre h)) : Lemma (post h h')
      = eliminate exists (m': mheap). r.repr m' h' /\ post h m'
        with id_repr r m' h' in
    FStar.Classical.impl_intro_gen #(lifted r pre h h' post) #(fun _ -> pre h ==> post h h')
      (fun q -> FStar.Classical.impl_intro_gen #(pre h) #(fun _ -> post h h') (e q))

let some_repr_id (r: rep mheap mheap) (h: mheap) (f: mheap -> prop)
  : Lemma (requires is_id r) (ensures some_repr r h f <==> f h)
  = id_repr r h h;
    let e (_: squash (some_repr r h f)) : Lemma (f h)
      = eliminate exists (m: mheap). r.repr m h /\ f m
        with id_repr r m h in
    FStar.Classical.impl_intro_gen #(some_repr r h f) #(fun _ -> f h) e

/// The world a concrete world of model heaps is.
let tview (cw: cworld mheap mheap) : world =
  { maj = cw.cmaj; yng = cw.cyng; roots = cw.croots; rem = cw.crem }

let world_eta (w: world) : Lemma (w == { maj = w.maj; yng = w.yng; roots = w.roots; rem = w.rem })
  = match w with | Mkworld _ _ _ _ -> ()

let cviews_id (r: rep mheap mheap) (cw: cworld mheap mheap) (w: world)
  : Lemma (requires is_id r) (ensures cviews r cw w <==> w == tview cw)
  = id_repr r w.maj cw.cmaj; id_yrepr r w.yng cw.cyng;
    id_repr r cw.cmaj cw.cmaj; id_yrepr r cw.cyng cw.cyng;
    world_eta w

let forall_views_id (r: rep mheap mheap) (cw: cworld mheap mheap) (f: world -> prop)
  : Lemma (requires is_id r) (ensures forall_views r cw f <==> f (tview cw))
  = cviews_id r cw (tview cw);
    let d (_: squash (f (tview cw))) (w: world) : Lemma (cviews r cw w ==> f w) = cviews_id r cw w in
    FStar.Classical.impl_intro_gen #(f (tview cw)) #(fun _ -> forall_views r cw f)
      (fun q -> FStar.Classical.forall_intro (d q))

/// The concrete world of a world.
let cw_of (w: world) : cworld mheap mheap = { cmaj = w.maj; cyng = w.yng; croots = w.roots; crem = w.rem }

let tview_cw_of (w: world) : Lemma (tview (cw_of w) == w) = world_eta w

/// The heap the representation picks for a model heap, and back, is itself.
let some_model_id (r: rep mheap mheap) (h: mheap)
  : Lemma (requires is_id r) (ensures some_model r h == Some h)
  = id_repr r h h;
    FStar.Classical.forall_intro (fun (m: mheap) -> id_repr r m h)

let some_heap_id (r: rep mheap mheap) (m: mheap)
  : Lemma (requires is_id r) (ensures some_heap r m == Some m)
  = id_repr r m m;
    FStar.Classical.forall_intro (fun (h: mheap) -> id_repr r m h)

#push-options "--fuel 1 --ifuel 1"
/// Promotion on the model heap itself (`alloc_fold` with the Fill taken
/// directly).
let rec plain_fold (#k: sweep_kind) (a: allocator mheap k) (ph: phase k.progress) (h: mheap) (st: a.state)
    (y: mheap) (ys: list nat) : GTot (option (mheap & a.state)) (decreases ys) =
  match ys with
  | [] -> Some (h, st)
  | o :: tl ->
    if wz_of y o >= 1 && tag_of y o <> infix_tag then
      (let (h', st', res) = a.alloc ph h st (wz_of y o) (tag_of y o) in
       match res with
       | NoRoom -> None
       | Ok c -> plain_fold a ph (fill h' c (fields_of y o)) st' y tl)
    else None

let rec alloc_fold_id (r: rep mheap mheap) (#k: sweep_kind) (a: allocator mheap k) (ph: phase k.progress)
    (h: mheap) (st: a.state) (y: mheap) (ys: list nat)
  : Lemma (requires is_id r)
          (ensures alloc_fold r a ph h st y ys == plain_fold a ph h st y ys)
          (decreases ys)
  = match ys with
    | [] -> ()
    | o :: tl ->
      if wz_of y o >= 1 && tag_of y o <> infix_tag then begin
        let (h', st', res) = a.alloc ph h st (wz_of y o) (tag_of y o) in
        match res with
        | NoRoom -> ()
        | Ok c ->
          some_model_id r h';
          some_heap_id r (fill h' c (fields_of y o));
          alloc_fold_id r a ph (fill h' c (fields_of y o)) st' y tl
      end
#pop-options
