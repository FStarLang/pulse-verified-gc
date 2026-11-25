/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWRun - building a pages witness run
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  A run is built as a tail from the initial configuration
/// (`RunApp.tail_ok`): `run_of` turns one into `run_ok` and `run_hyps`, and
/// `tail_app` joins two.  The conditions of one event (`RunApp.conds`:
/// enabled, in the style, the program's obligations, the contracts) on a
/// described configuration, one lemma per kind of event, with the
/// obligations read on the description's world (`PWDesc.wd`).  And what is
/// reachable there: a root, a field of a reachable block, and every
/// reachable block inside a set closed under the edges.

module GC.Spec.Top.PWRun

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.ByteRep
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.Run
open GC.Spec.Top.PWDesc
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module RA = GC.Spec.Top.RunApp
module RF = GC.Spec.Top.RunFacts
module PWM = GC.Spec.Top.PWMinor

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Tails
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec tail_app (sty: style) (x: config pc) (l1 l2: list event)
  : Lemma (requires RA.tail_ok pc sty x l1 /\ RA.tail_ok pc sty (exec pc x l1) l2)
          (ensures RA.tail_ok pc sty x (L.append l1 l2)) (decreases l1)
  = match l1 with
    | [] -> ()
    | e :: tl -> tail_app sty (step pc x e) tl l2

let rec exec_app (x: config pc) (l1 l2: list event)
  : Lemma (ensures exec pc x (L.append l1 l2) == exec pc (exec pc x l1) l2) (decreases l1)
  = match l1 with
    | [] -> ()
    | e :: tl -> exec_app (step pc x e) tl l2

let tail_nil (sty: style) (x: config pc) : Lemma (RA.tail_ok pc sty x [] /\ exec pc x [] == x) = ()

let tail_one (sty: style) (x: config pc) (e: event)
  : Lemma (requires RA.conds pc sty x e) (ensures RA.tail_ok pc sty x [e] /\ exec pc x [e] == step pc x e)
  = tail_nil sty (step pc x e);
    assert (RA.tail_ok pc sty x [e] == (RA.conds pc sty x e /\ RA.tail_ok pc sty (step pc x e) []));
    assert (exec pc x [e] == exec pc (step pc x e) [])

let tail_cons (sty: style) (x: config pc) (e: event) (tl: list event)
  : Lemma (requires RA.conds pc sty x e /\ RA.tail_ok pc sty (step pc x e) tl)
          (ensures RA.tail_ok pc sty x (e :: tl) /\ exec pc x (e :: tl) == exec pc (step pc x e) tl)
  = ()
#pop-options

/// **A tail from the initial configuration is a run.**
#push-options "--fuel 1"
let run_of (sty: style) (es: list event)
  : Lemma (requires cok /\ RA.tail_ok pc sty (init_config pc msize ywords) es)
          (ensures run_ok pc sty msize ywords es /\ run_hyps pc msize ywords es)
  = cok_ok ();
    assert (T.init_at byte_rep pa msize);
    assert (R.yinit_ok byte_rep ywords);
    assert (run_ok pc sty msize ywords [] /\ run_hyps pc msize ywords []);
    RF.at_zero pc msize ywords [];
    RA.run_of_tail pc sty msize ywords [] 0 es
#pop-options

/// The configuration after a run's first events.
let at_tail (es: list event) (i: nat) (x: config pc)
  : Lemma (requires x == exec pc (init_config pc msize ywords) (take i es))
          (ensures at pc msize ywords es i == x)
  = ()

/// ---------------------------------------------------------------------------
/// The conditions of one event
/// ---------------------------------------------------------------------------

let conds_of (sty: style) (x: config pc) (d: dsc) (e: event)
  : Lemma (requires cok /\ holds x d /\ enabled pc x e /\ style_ok sty x e /\ mutator_ok_w pc (wd x d) e)
          (ensures RA.conds pc sty x e)
  = mutator_wd x d e;
    cok_hyps x e

/// The collector's events need nothing of the program.
let mut_coll (x: config pc) (d: dsc) (e: event)
  : Lemma (requires not (is_mutator_event e)) (ensures mutator_ok_w pc (wd x d) e)
  = ()

let style_coll (sty: style) (x: config pc) (e: event)
  : Lemma (requires not (is_mutator_event e)) (ensures style_ok sty x e)
  = ()

let style_idle (sty: style) (x: config pc) (d: dsc) (e: event)
  : Lemma (requires holds x d /\ d.dk == DI) (ensures style_ok sty x e)
  = holds_elim x d

let style_inc (x: config pc) (e: event) : Lemma (style_ok Incremental x e) = ()

let enabled_plain (x: config pc) (d: dsc) (e: event)
  : Lemma (requires holds x d /\ (EAlloc? e \/ EWrite? e \/ ERead? e \/ ERoots? e \/ EMinor? e))
          (ensures enabled pc x e)
  = holds_elim x d

let enabled_start (x: config pc) (d: dsc)
  : Lemma (requires holds x d /\ d.dk == DI) (ensures enabled pc x EStart)
  = holds_elim x d

let enabled_slice (x: config pc) (d: dsc)
  : Lemma (requires holds x d /\ d.dk == DM /\ ~(T.no_grey (mx x))) (ensures enabled pc x ESlice)
  = holds_elim x d; mark_done_wd x d

let enabled_hand (x: config pc) (d: dsc)
  : Lemma (requires holds x d /\ d.dk == DM /\ T.no_grey (mx x)) (ensures enabled pc x EHandover)
  = holds_elim x d; mark_done_wd x d

let enabled_yalloc (x: config pc) (d: dsc) (sz: M.size_t) (tag: M.tag_t) (vs: list M.value) (o: nat) (ms': GC.Gen.MinorHeap.minor_state)
  : Lemma (requires holds x d /\ GC.Spec.Top.Young.yalloc d.dys sz tag vs == Some (o, ms'))
          (ensures enabled pc x (EYoungAlloc sz tag vs))
  = holds_elim x d

/// ---------------------------------------------------------------------------
/// What is reachable
/// ---------------------------------------------------------------------------

/// A block in use is its own address.
let res_iu (x: config pc) (o: nat)
  : Lemma (requires iu x o == true) (ensures M.resolve (mx x) o == Some o /\ M.is_block (mx x) o)
  = iu_def x o

/// A root at a block in use: reachable.
let reach_r (x: config pc) (d: dsc) (o: nat)
  : Lemma (requires holds x d /\ L.memP (M.VPtr (M.Major o)) d.drt /\ iu x o == true)
          (ensures M.reachable (wd x d) o)
  = res_iu x o;
    reach_root (wd x d) o o

/// Field `i` of a reachable usable block, pointing to `a` resolving to `o'`:
/// reachable.
let reach_f (x: config pc) (d: dsc) (o i a o': nat)
  : Lemma (requires holds x d /\ M.reachable (wd x d) o /\ Some? (d.db o) /\ usable d (Some?.v (d.db o)) /\
                    M.scannable (Some?.v (d.db o)).bt /\ i < (Some?.v (d.db o)).bw /\
                    vi (Some?.v (d.db o)).bf i == M.VPtr (M.Major a) /\ M.resolve (mx x) a == Some o')
          (ensures M.reachable (wd x d) o')
  = blk x d o;
    reach_field (wd x d) o i a o'

/// A value the program may hold: an integer, or a pointer resolving to a
/// reachable block.
let vok_ptr (x: config pc) (d: dsc) (a o: nat)
  : Lemma (requires M.resolve (mx x) a == Some o /\ M.reachable (wd x d) o)
          (ensures value_ok (wd x d) (M.VPtr (M.Major a)))
  = ()

/// Every reachable block in a set `s` of usable blocks holding the roots'
/// targets and closed under fields.
let reach_closed (x: config pc) (d: dsc) (s: nat -> prop)
  : Lemma (requires holds x d /\
                    (forall (o: nat). M.outside_ref (wd x d) o ==> s o) /\
                    (forall (o: nat). s o ==> Some? (d.db o) /\ usable d (Some?.v (d.db o))) /\
                    (forall (o i a o': nat). s o /\ i < (Some?.v (d.db o)).bw /\ M.scannable (Some?.v (d.db o)).bt /\
                       vi (Some?.v (d.db o)).bf i == M.VPtr (M.Major a) /\ M.resolve (mx x) a == Some o' ==> s o'))
          (ensures forall (o: nat). M.reachable (wd x d) o ==> s o)
  = let edge (o o': nat) : Lemma (requires s o /\ M.major_edge (mx x) o o') (ensures s o')
      = blk x d o;
        eliminate exists (i a: nat). M.ptr_field (mx x) o i /\ M.field (mx x) o i == M.VPtr (M.Major a) /\
                                     M.resolve (mx x) a == Some o'
        with () in
    FStar.Classical.forall_intro_2 (fun o o' -> FStar.Classical.move_requires (edge o) o');
    reach_in (wd x d) s

/// A sound value for the allocator: a pointer resolving to a usable block.
let sound_p (x: config pc) (d: dsc) (a o: nat)
  : Lemma (requires holds x d /\ Some? (d.db o) /\ usable d (Some?.v (d.db o)) /\ M.resolve (mx x) a == Some o)
          (ensures T.sound_value pa x.ph (stx x) x.w.cmaj (mx x) (M.VPtr (M.Major a)))
  = PWM.usable_lt x d o;
    blk x d o

/// ---------------------------------------------------------------------------
/// Relabelling
/// ---------------------------------------------------------------------------

let relab (d: dsc) (y: nat) (lv: bool) : GTot dsc =
  { d with db = (fun (z: nat) -> if z = y then (match d.db z with Some b -> Some ({ b with blv = lv }) | None -> None)
                                 else d.db z) }

/// Outside the sweep, live or garbage reads the same.
let relabel (x: config pc) (d: dsc) (y: nat) (lv: bool)
  : Lemma (requires holds x d /\ d.dk =!= DS) (ensures holds x (relab d y lv))
  = holds_elim x d;
    let d' = relab d y lv in
    let bl (z: nat) : Lemma (Some? (d'.db z) ==> bk x d' z (Some?.v (d'.db z)))
      = if Some? (d.db z) then holds_blk x d z in
    FStar.Classical.forall_intro bl;
    let des (z: nat) : Lemma (iu x z == true ==> Some? (d'.db z))
      = if iu x z then holds_iu x d z in
    FStar.Classical.forall_intro des;
    holds_intro x d'

/// ---------------------------------------------------------------------------
/// The model after a write
/// ---------------------------------------------------------------------------

module PWMu = GC.Spec.Top.PWMut
module BB = GC.Spec.Top.ByteBarrier

/// A block in use is still its own address after the write.
let res_mw_blk (x: config pc) (o i: nat) (v: M.value) (t: nat)
  : Lemma (requires iu x t == true) (ensures M.resolve (PWMu.mw x o i v) t == Some t)
  = iu_def x t;
    BB.tdark_shape (T.is_marking x.ph) (mx x) o i

/// The infix pointer into a closure the write does not touch.
let res_mw_infix (x: config pc) (d: dsc) (o i: nat) (v: M.value) (k: nat)
  : Lemma (requires holds x d /\ Some? (d.db o) /\ usable d (Some?.v (d.db o)) /\ i < (Some?.v (d.db o)).bw /\
                    PWM.kdesc d k /\ o <> k)
          (ensures M.resolve (PWMu.mw x o i v) (k + 2) == Some k)
  = holds_elim x d;
    blk x d k;
    blk x d o;
    BB.tdark_shape (T.is_marking x.ph) (mx x) o i;
    PWMu.wf_shape (mx x) (PWMu.mw x o i v);
    if k + 2 = o + 1 + i then begin
      assert (M.covers (mx x) k (k + 2));
      assert (M.covers (mx x) o (k + 2))
    end;
    assert (M.field (PWMu.mw x o i v) k 1 == M.field (mx x) k 1);
    res_infix (PWMu.mw x o i v) k

/// A pointer to a block the program may use is sound after the write.
let sound_mw (x: config pc) (d: dsc) (o i: nat) (v: M.value) (a t: nat)
  : Lemma (requires holds x d /\ Some? (d.db t) /\ usable d (Some?.v (d.db t)) /\ not (T.is_marking x.ph) /\
                    M.resolve (PWMu.mw x o i v) a == Some t)
          (ensures T.sound_value pa x.ph (stx x) x.w.cmaj (PWMu.mw x o i v) (M.VPtr (M.Major a)))
  = PWM.usable_lt x d t;
    blk x d t;
    iu_def x t;
    BB.tdark_shape (T.is_marking x.ph) (mx x) o i

/// ---------------------------------------------------------------------------
/// No allocation fails
/// ---------------------------------------------------------------------------

/// No allocation fails at this step, sealed.
[@@"opaque_to_smt"]
let asucc (x: config pc) (e: event) : prop = GC.Spec.Top.Transp.alloc_succeeds x e

let asucc_def (x: config pc) (e: event) : Lemma (asucc x e <==> GC.Spec.Top.Transp.alloc_succeeds x e)
  = reveal_opaque (`%asucc) (asucc x e)

let rec nf_tail (x: config pc) (tl: list event) : Tot prop (decreases tl) =
  match tl with
  | [] -> True
  | e :: r -> asucc x e /\ nf_tail (step pc x e) r

#push-options "--fuel 1"
let rec nf_idx (x: config pc) (tl: list event) (k: nat)
  : Lemma (requires nf_tail x tl /\ k < L.length tl)
          (ensures asucc (exec pc x (take k tl)) (L.index tl k)) (decreases tl)
  = match tl with
    | e :: r -> if k = 0 then () else (let k' : nat = k - 1 in nf_idx (step pc x e) r k')

let rec nf_app (x: config pc) (l1 l2: list event)
  : Lemma (requires nf_tail x l1 /\ nf_tail (exec pc x l1) l2) (ensures nf_tail x (L.append l1 l2)) (decreases l1)
  = match l1 with
    | [] -> ()
    | e :: tl -> nf_app (step pc x e) tl l2

let nf_cons (x: config pc) (e: event) (tl: list event)
  : Lemma (requires GC.Spec.Top.Transp.alloc_succeeds x e /\ nf_tail (step pc x e) tl) (ensures nf_tail x (e :: tl))
  = asucc_def x e

let nf_coll (x: config pc) (e: event) : Lemma (requires not (EAlloc? e)) (ensures GC.Spec.Top.Transp.alloc_succeeds x e)
  = ()
#pop-options

/// **No allocation of the run fails.**
let no_fail_of (es: list event)
  : Lemma (requires nf_tail (init_config pc msize ywords) es)
          (ensures GC.Spec.Top.Transp.no_fail pc msize ywords es)
  = let one (i: nat) : Lemma (i < L.length es ==>
                              GC.Spec.Top.Transp.alloc_succeeds (at pc msize ywords es i) (ev es i))
      = if i < L.length es then begin
          nf_idx (init_config pc msize ywords) es i;
          asucc_def (at pc msize ywords es i) (ev es i)
        end in
    FStar.Classical.forall_intro one

/// ---------------------------------------------------------------------------
/// Forwarding values without young pointers
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec map_fwd (y: M.mheap) (f: nat -> option nat) (rs: list M.value)
  : Lemma (requires GC.Spec.Top.FFWStep.no_young rs == true) (ensures L.map (T.fwdv y f) rs == rs) (decreases rs)
  = match rs with
    | [] -> ()
    | _ :: tl -> map_fwd y f tl
#pop-options
