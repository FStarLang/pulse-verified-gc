/// ---------------------------------------------------------------------------
/// GC.Spec.Top.RunFacts - unfolding a run, and worlds that read the same
/// ---------------------------------------------------------------------------
///
/// Design doc §14.  Facts about `GC.Spec.Top.Run` that the witness runs of
/// every instance use:
///   - `at_succ`: the configuration after `i + 1` events is one step from
///     the one after `i`;
///   - `wheq`: two model worlds with the same reading (heaps equal word by
///     word, same roots and remembered set) have the same reachable and
///     young-reachable objects, values the program may hold, and mutator
///     obligations (`mutator_wheq`).  A configuration's world `vw x` is any
///     world that represents it, so a statement about one such world is one
///     about `vw x`.

module GC.Spec.Top.RunFacts

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
module L = FStar.List.Tot

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// One event at a time
/// ---------------------------------------------------------------------------

#push-options "--fuel 2"
let rec take_snoc (#t: Type) (i: nat) (l: list t)
  : Lemma (requires i < L.length l) (ensures take (i + 1) l == L.append (take i l) [L.index l i]) (decreases l)
  = match l with
    | _ :: tl -> if i = 0 then () else take_snoc (i - 1) tl
#pop-options

let rec exec_append (c: comps) (x: config c) (a b: list event)
  : Lemma (ensures exec c x (L.append a b) == exec c (exec c x a) b) (decreases a)
  = match a with
    | [] -> ()
    | e :: tl -> exec_append c (step c x e) tl b

/// **The configuration after `i + 1` events.**
#push-options "--fuel 2"
let at_succ (c: comps) (n ny: nat) (es: list event) (i: nat)
  : Lemma (requires i < L.length es) (ensures at c n ny es (i + 1) == step c (at c n ny es i) (ev es i))
  = take_snoc i es;
    exec_append c (init_config c n ny) (take i es) [ev es i]
#pop-options

let at_zero (c: comps) (n ny: nat) (es: list event) : Lemma (at c n ny es 0 == init_config c n ny)
  = match es with [] -> () | _ -> ()

/// ---------------------------------------------------------------------------
/// Worlds that read the same
/// ---------------------------------------------------------------------------

let wheq (w w': world) : prop =
  heq w.maj w'.maj /\ heq w.yng w'.yng /\ w.roots == w'.roots /\ w.rem == w'.rem

let resolve_heq (h h': mheap) (a: nat) : Lemma (requires heq h h') (ensures resolve h a == resolve h' a) = ()

let root_wheq (w w': world) (o a: nat)
  : Lemma (requires wheq w w' /\ L.memP (VPtr (Major a)) w.roots /\ resolve w.maj a == Some o)
          (ensures root_ref w' o)
  = resolve_heq w.maj w'.maj a

let yref_wheq (w w': world) (o y i a: nat)
  : Lemma (requires wheq w w' /\ ptr_field w.yng y i /\ field w.yng y i == VPtr (Major a) /\
                    resolve w.maj a == Some o)
          (ensures young_ref w' o)
  = resolve_heq w.maj w'.maj a;
    assert (ptr_field w'.yng y i /\ field w'.yng y i == VPtr (Major a))

let outside_wheq (w w': world) (o: nat)
  : Lemma (requires wheq w w') (ensures outside_ref w o ==> outside_ref w' o)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (root_wheq w w' o));
    FStar.Classical.forall_intro_3 (fun y i a -> FStar.Classical.move_requires (yref_wheq w w' o y i) a)

let edge1 (h h': mheap) (o o' i a: nat)
  : Lemma (requires heq h h' /\ ptr_field h o i /\ field h o i == VPtr (Major a) /\ resolve h a == Some o')
          (ensures major_edge h' o o')
  = resolve_heq h h' a;
    assert (ptr_field h' o i /\ field h' o i == VPtr (Major a))

let edge_wheq (h h': mheap) (o o': nat)
  : Lemma (requires heq h h') (ensures major_edge h o o' ==> major_edge h' o o')
  = FStar.Classical.forall_intro_2 (fun i a -> FStar.Classical.move_requires (edge1 h h' o o' i) a)

let rec reach_wheq (w w': world) (o: nat) (r: reach w o)
  : Lemma (requires wheq w w') (ensures reachable w' o) (decreases r)
  = match r with
    | RBase _ _ ->
      outside_wheq w w' o;
      let r' : reach w' o = RBase o () in ()
    | RStep x _ r0 _ ->
      reach_wheq w w' x r0;
      edge_wheq w.maj w'.maj x o;
      let r0' = FStar.IndefiniteDescription.indefinite_description_ghost (reach w' x) (fun _ -> True) in
      let r' : reach w' o = RStep x o r0' () in ()

let reachable_wheq (w w': world) (o: nat)
  : Lemma (requires wheq w w') (ensures reachable w o <==> reachable w' o)
  = let f (r: reach w o) : Lemma (reachable w' o) = reach_wheq w w' o r in
    let g (r: reach w' o) : Lemma (reachable w o) = reach_wheq w' w o r in
    FStar.Classical.forall_intro f;
    FStar.Classical.forall_intro g

let yedge1 (h h': mheap) (o o' i a: nat)
  : Lemma (requires heq h h' /\ ptr_field h o i /\ field h o i == VPtr (Young a) /\ resolve h a == Some o')
          (ensures young_edge h' o o')
  = resolve_heq h h' a;
    assert (ptr_field h' o i /\ field h' o i == VPtr (Young a))

let young_edge_wheq (y y': mheap) (o o': nat)
  : Lemma (requires heq y y') (ensures young_edge y o o' ==> young_edge y' o o')
  = FStar.Classical.forall_intro_2 (fun i a -> FStar.Classical.move_requires (yedge1 y y' o o' i) a)

let rec yreach_wheq (w w': world) (o: nat) (r: yreach w o)
  : Lemma (requires wheq w w') (ensures yreachable w' o) (decreases r)
  = match r with
    | YRoot _ a _ ->
      resolve_heq w.yng w'.yng a;
      let r' : yreach w' o = YRoot o a () in ()
    | YOld _ x i a r0 _ ->
      reach_wheq w w' x r0;
      resolve_heq w.yng w'.yng a;
      let r0' = FStar.IndefiniteDescription.indefinite_description_ghost (reach w' x) (fun _ -> True) in
      let r' : yreach w' o = YOld o x i a r0' () in ()
    | YStep x _ r0 _ ->
      yreach_wheq w w' x r0;
      young_edge_wheq w.yng w'.yng x o;
      let r0' = FStar.IndefiniteDescription.indefinite_description_ghost (yreach w' x) (fun _ -> True) in
      let r' : yreach w' o = YStep x o r0' () in ()

let yreachable_wheq (w w': world) (o: nat)
  : Lemma (requires wheq w w') (ensures yreachable w o <==> yreachable w' o)
  = let f (r: yreach w o) : Lemma (yreachable w' o) = yreach_wheq w w' o r in
    let g (r: yreach w' o) : Lemma (yreachable w o) = yreach_wheq w' w o r in
    FStar.Classical.forall_intro f;
    FStar.Classical.forall_intro g

let value_ok_wheq (w w': world) (v: value)
  : Lemma (requires wheq w w') (ensures value_ok w v <==> value_ok w' v)
  = match v with
    | VPtr (Major a) ->
      resolve_heq w.maj w'.maj a;
      FStar.Classical.forall_intro (FStar.Classical.move_requires (reachable_wheq w w'))
    | VPtr (Young a) ->
      resolve_heq w.yng w'.yng a;
      FStar.Classical.forall_intro (FStar.Classical.move_requires (yreachable_wheq w w'))
    | _ -> ()

/// **The program's obligations read the world through its reading.**
#push-options "--z3rlimit 40"
let mutator_wheq (c: comps) (w w': world) (e: event)
  : Lemma (requires wheq w w' /\ mutator_ok_w c w e) (ensures mutator_ok_w c w' e)
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (value_ok_wheq w w'));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (reachable_wheq w w'));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (yreachable_wheq w w'))
#pop-options

/// A world representing the configuration gives its obligations.
let mutator_of_view (#c: comps) (x: config c) (w: world) (e: event)
  : Lemma (requires views x w /\ mutator_ok_w c w e /\
                    (forall (w1 w2: world). views x w1 /\ views x w2 ==> wheq w1 w2))
          (ensures mutator_ok x e)
  = vw_views x;
    mutator_wheq c w (vw x) e

/// ---------------------------------------------------------------------------
/// The contracts at every step
/// ---------------------------------------------------------------------------

/// **The components' contracts give the hypotheses of every step of every
/// run** (`run_hyps`, the hypotheses of `gc_correct_local`).
let run_hyps_of_ok (c: comps) (n ny: nat) (es: list event)
  : Lemma (requires components_ok c) (ensures run_hyps c n ny es)
  = let f (i: nat) : Lemma (i < L.length es ==> hyps_at c (at c n ny es i) (ev es i))
      = if i < L.length es then hyps_of_ok c (at c n ny es i) (ev es i) in
    FStar.Classical.forall_intro f;
    assert (init_at c.r c.a n);
    assert (yinit_ok c.r ny)
