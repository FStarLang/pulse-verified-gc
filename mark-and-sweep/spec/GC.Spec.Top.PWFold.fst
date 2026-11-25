/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PWFold - a minor collection of a pages witness run has room
/// ---------------------------------------------------------------------------
///
/// Design doc §17.  The witness runs' nurseries hold at most two one-field
/// blocks, at young addresses 0 and 2, each holding an integer or the
/// infix pointer `k + 2` into a live closure `k` (three fields, the second
/// the infix header of offset 2).  Then:
///   - `fold_some`: the contract's `alloc_fold` over any list of them
///     without repeats succeeds: each allocation has room while the budget
///     leaves a free page (`PWPages.room_of`), and keeps the allocator's
///     invariant, the walk and the closure (`fold_one`).  So `OutOfRoom` is
///     never justified;
///   - `minor_kinds`: the collection costs at most two pages of the budget:
///     its page state is the replay of its queue (`PromoteRun.qok`), whose
///     entries are distinct nursery objects (`replay_kinds`).

module GC.Spec.Top.PWFold

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.MinorHeap
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteRep
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.Run
open GC.Spec.Top.PWDesc
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module Y = GC.Spec.Top.Young
module BB = GC.Spec.Top.ByteBarrier
module PIn = GC.Spec.Top.PagesInst
module PWP = GC.Spec.Top.PWPages
module PWA = GC.Spec.Top.PWAlloc
module FWS = GC.Spec.Top.FFWStep
module O = GC.Spec.Top.PagesOor
module P = GC.Spec.Pages.Promote
module PR = GC.Spec.Top.PromoteRun
module PRe = GC.Spec.Top.PagesReplay
module PM = GC.Spec.Top.PagesMinor
module LV = GC.Spec.Top.PagesLive
module Q = GC.Spec.Top.PagesQueue
module PC = GC.Spec.Top.PromoteCopy
module BM = GC.Spec.Top.ByteMark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The nursery
/// ---------------------------------------------------------------------------

/// A young field the runs store: an integer, or the infix pointer into `k`.
let yval (k: nat) (v: M.value) : bool =
  match v with
  | M.VInt _ -> true
  | M.VPtr (M.Major a) -> a = k + 2
  | _ -> false

/// The nursery: blocks at 0 and 2 only, one field each, tag 0.
let ynice (k: nat) (y: M.mheap) : prop =
  (forall (o: nat). M.is_block y o ==> (o == 0 \/ o == 2) /\ M.wz_of y o == 1 /\ M.tag_of y o == 0 /\
                                       yval k (M.field y o 0))

/// The closure `k`, live, in a model of the major heap.
let kok (ph: T.phase pprog) (st: pst) (h: heap) (k: nat) : prop =
  let m = cabs h in
  M.well_formed m /\ M.is_block m k /\ M.tag_of m k == M.closure_tag /\ M.wz_of m k == 3 /\
  M.field m k 1 == M.infix_word 2 /\ T.live_target pa ph st h m k

/// The state a fold step needs.
let fs (ph: T.phase pprog) (h: heap) (st: pst) (k j: nat) : prop =
  pinv ph h st /\ PWP.kinds_ok st.ps j /\ kok ph st h k

#push-options "--fuel 2"
let fields1 (y: M.mheap) (o: nat) : Lemma (M.fields_of y o == [M.field y o 0] \/ M.wz_of y o =!= 1)
  = ()
#pop-options

/// The young field is a value the allocator may store.
let sound_y (ph: T.phase pprog) (st: pst) (h: heap) (k: nat) (v: M.value)
  : Lemma (requires kok ph st h k /\ yval k v) (ensures T.sound_value pa ph st h (cabs h) v)
  = match v with
    | M.VPtr (M.Major a) -> res_infix (cabs h) k
    | _ -> ()

let stor_y (ph: T.phase pprog) (st: pst) (h: heap) (k: nat) (v: M.value)
  : Lemma (requires kok ph st h k /\ yval k v /\ (match v with M.VInt n -> storable_w v | _ -> True))
          (ensures storable_w v)
  = match v with
    | M.VPtr (M.Major a) -> assert (M.covers (cabs h) k (k + 3)); major_storable (k + 2)
    | _ -> ()

/// ---------------------------------------------------------------------------
/// One step of the fold
/// ---------------------------------------------------------------------------

/// The smallest class bound: every block of at most 15 fields is small.
let smax () : Lemma (17 <= small_max)
  = params_ok ();
    GC.Spec.SizeClass.n_small_u64_v ()

/// The allocation's contract, at one step.
/// The allocator's result, by parts.
let fh (ph: T.phase pprog) (h: heap) (st: pst) : GTot heap = let (h', _, _) = pa.T.alloc ph h st 1 0 in h'
let fst' (ph: T.phase pprog) (h: heap) (st: pst) : GTot pst = let (_, s', _) = pa.T.alloc ph h st 1 0 in s'
let fr (ph: T.phase pprog) (h: heap) (st: pst) : GTot T.result = let (_, _, r) = pa.T.alloc ph h st 1 0 in r

let f_parts (ph: T.phase pprog) (h: heap) (st: pst)
  : Lemma (pa.T.alloc ph h st 1 0 == (fh ph h st, fst' ph h st, fr ph h st)) = ()

let fpost (ph: T.phase pprog) (h: heap) (st: pst) (m': M.mheap) : prop =
  T.alloc_post byte_rep pa ph h st 1 0 (fh ph h st) (fst' ph h st) (fr ph h st) (cabs h) m'

#push-options "--fuel 2"
let mem1 (u v: M.value) : Lemma (L.memP u [v] ==> u == v) = ()
let len1 (v: M.value) : Lemma (L.length [v] == 1) = ()
#pop-options

/// The invariant after the Fill.
#push-options "--fuel 1"
let post_inv (ph: T.phase pprog) (h: heap) (st: pst) (k: nat) (v: M.value) (m': M.mheap) (h'': heap)
  : Lemma (requires fpost ph h st m' /\ T.Ok? (fr ph h st) /\ kok ph st h k /\ yval k v /\
                    brepr (M.fill m' (T.Ok?._0 (fr ph h st)) [v]) h'')
          (ensures pinv ph h'' (fst' ph h st))
  = sound_y ph st h k v;
    FStar.Classical.forall_intro (fun (u: M.value) -> mem1 u v);
    len1 v;
    let c = T.Ok?._0 (fr ph h st) in
    assert (forall (u: M.value). L.memP u [v] ==> T.sound_value pa ph st h (cabs h) u);
    assert (byte_rep.R.repr (M.fill m' c [v]) h'');
    assert (forall (vs: list M.value) (g: heap).
              L.length vs == 1 /\ (M.scannable 0 ==> (forall (u: M.value). L.memP u vs ==> T.sound_value pa ph st h (cabs h) u)) /\
              byte_rep.R.repr (M.fill m' c vs) g ==> pa.T.inv ph g (fst' ph h st));
    assert (pa.T.inv ph h'' (fst' ph h st))
#pop-options

/// The closure, the new block and the walk, after the allocation.
let post_k (ph: T.phase pprog) (h: heap) (st: pst) (k: nat) (m': M.mheap)
  : Lemma (requires fpost ph h st m' /\ T.Ok? (fr ph h st) /\ kok ph st h k)
          (ensures (let c = T.Ok?._0 (fr ph h st) in
                    M.well_formed m' /\ M.is_block m' c /\ M.wz_of m' c == 1 /\
                    M.same_block (cabs h) m' k /\ c <> k /\
                    (T.in_use pa (fst' ph h st) (fh ph h st) m' k <==> T.in_use pa st h (cabs h) k)))
  = let c = T.Ok?._0 (fr ph h st) in
    assert (T.in_use pa st h (cabs h) k);
    PWA.was_free st h (cabs h) m' c

#push-options "--z3rlimit 40 --fuel 1"
let fold_next (ph: T.phase pprog) (h: heap) (st: pst) (k j: nat) (v: M.value) (m': M.mheap) (h'': heap)
  : Lemma (requires fs ph h st k j /\ yval k v /\ T.Ok? (fr ph h st) /\ PWP.kinds_ok (fst' ph h st).ps (j + 1) /\
                    brepr m' (fh ph h st) /\ fpost ph h st m' /\
                    brepr (M.fill m' (T.Ok?._0 (fr ph h st)) [v]) h'')
          (ensures fs ph h'' (fst' ph h st) k (j + 1))
  = let c = T.Ok?._0 (fr ph h st) in
    let h' = fh ph h st in
    let st' = fst' ph h st in
    post_inv ph h st k v m' h'';
    post_k ph h st k m';
    len1 v;
    let m = cabs h in
    PWA.fill_wf m' c [v];
    PIn.wf_heq (M.fill m' c [v]) (cabs h'');
    PWA.fill_other m' c k 1 [v];
    PWA.iu_any st' h'' (cabs h'') k;
    PWA.iu_any st' h' m' k;
    PWA.iu_any st h m k;
    assert (M.field (cabs h'') k 1 == M.field m k 1);
    assert ((cabs h'').M.hd k == m.M.hd k)
#pop-options

let fold_alloc (ph: T.phase pprog) (h: heap) (st: pst) (k j: nat) (v: M.value)
  : Lemma (requires cok /\ fs ph h st k j /\ j < n_pages)
          (ensures T.Ok? (fr ph h st) /\ PWP.kinds_ok (fst' ph h st).ps (j + 1) /\
                   (exists (m': M.mheap). brepr m' (fh ph h st) /\ fpost ph h st m'))
  = smax ();
    f_parts ph h st;
    PWP.room_of ph h st 1 j;
    PWP.palloc_kinds ph h st 1 0 j;
    cok_alloc ph h st 1 0;
    brepr_cabs h;
    assert (T.alloc_pre pa ph h st 0 (cabs h));
    assert (exists (m': M.mheap). brepr m' (fh ph h st) /\ fpost ph h st m')

/// One step of `alloc_fold`, unfolded.
#push-options "--fuel 1"
let fold_unfold (ph: T.phase pprog) (h: heap) (st: pst) (y: M.mheap) (o: nat) (tl: list nat) (h2: heap)
  : Lemma (requires M.wz_of y o == 1 /\ M.tag_of y o == 0 /\ T.Ok? (fr ph h st) /\
                    M.fields_of y o == [M.field y o 0] /\ Some? (T.some_model byte_rep (fh ph h st)) /\
                    T.some_heap byte_rep (M.fill (Some?.v (T.some_model byte_rep (fh ph h st))) (T.Ok?._0 (fr ph h st))
                                                 [M.field y o 0]) == Some h2)
          (ensures T.alloc_fold byte_rep pa ph h st y (o :: tl) == T.alloc_fold byte_rep pa ph h2 (fst' ph h st) y tl)
  = f_parts ph h st
#pop-options

/// Some heap represents the Fill.
let fill_heap (h': heap) (m': M.mheap) (c: nat) (v: M.value)
  : Lemma (requires brepr m' h' /\ M.is_block m' c /\ M.wz_of m' c == 1 /\ storable_w v)
          (ensures exists (h'': heap). brepr (M.fill m' c [v]) h'')
  = len1 v;
    FStar.Classical.forall_intro (fun (u: M.value) -> mem1 u v);
    assert (M.wz_of (cabs h') c == 1);
    BB.binit_from_ok h' [] c 0 [v];
    BB.fill_at_zero (cabs h') c [v];
    let (h'', _) = BB.binit h' [] c [v] in
    R.heq_sym m' (cabs h');
    FWS.fill_heq (cabs h') m' c [v];
    assert (R.heq (cabs h'') (BB.fill_at (cabs h') c 0 [v]));
    assert (brepr (M.fill m' c [v]) h'')

/// The heap `alloc_fold` picks after the Fill.
let some_fill (h': heap) (m'': M.mheap) (c: nat) (v: M.value) (h3: heap)
  : Lemma (requires brepr (M.fill m'' c [v]) h3)
          (ensures Some? (T.some_heap byte_rep (M.fill m'' c [v])) /\
                   T.some_heap byte_rep (M.fill m'' c [v]) == Some (Some?.v (T.some_heap byte_rep (M.fill m'' c [v]))) /\
                   brepr (M.fill m'' c [v]) (Some?.v (T.some_heap byte_rep (M.fill m'' c [v]))))
  = O.some_heap_is (M.fill m'' c [v]) h3

/// The step, once the contract's model and a heap of the Fill are chosen.
#push-options "--z3rlimit 40 --fuel 1"
let fold_inner (ph: T.phase pprog) (h: heap) (st: pst) (k j: nat) (y: M.mheap) (o: nat) (tl: list nat)
               (m' m'': M.mheap) (h3: heap)
  : Lemma (requires fs ph h st k j /\ ynice k y /\ M.is_block y o /\
                    M.fields_of y o == [M.field y o 0] /\
                    T.Ok? (fr ph h st) /\ PWP.kinds_ok (fst' ph h st).ps (j + 1) /\
                    brepr m' (fh ph h st) /\ fpost ph h st m' /\
                    T.some_model byte_rep (fh ph h st) == Some m'' /\ brepr m'' (fh ph h st) /\
                    brepr (M.fill m'' (T.Ok?._0 (fr ph h st)) [M.field y o 0]) h3)
          (ensures exists (h2: heap) (st2: pst). fs ph h2 st2 k (j + 1) /\
                     T.alloc_fold byte_rep pa ph h st y (o :: tl) == T.alloc_fold byte_rep pa ph h2 st2 y tl)
  = let v = M.field y o 0 in
    let h' = fh ph h st in
    let c = T.Ok?._0 (fr ph h st) in
    post_k ph h st k m';
    some_fill h' m'' c v h3;
    let h2 = Some?.v (T.some_heap byte_rep (M.fill m'' c [v])) in
    R.heq_sym m' (cabs h'); R.heq_trans m'' (cabs h') m';
    FWS.fill_heq m'' m' c [v];
    R.heq_sym (M.fill m'' c [v]) (M.fill m' c [v]);
    R.heq_trans (M.fill m' c [v]) (M.fill m'' c [v]) (cabs h2);
    fold_next ph h st k j v m' h2;
    fold_unfold ph h st y o tl h2
#pop-options

/// **One step**: the fold moves on to a state that again has what it needs.
#push-options "--z3rlimit 40"
let fold_one (ph: T.phase pprog) (h: heap) (st: pst) (k j: nat) (y: M.mheap) (o: nat) (tl: list nat)
  : Lemma (requires cok /\ fs ph h st k j /\ j < n_pages /\ ynice k y /\ M.is_block y o /\
                    storable_w (M.field y o 0))
          (ensures exists (h2: heap) (st2: pst). fs ph h2 st2 k (j + 1) /\
                     T.alloc_fold byte_rep pa ph h st y (o :: tl) == T.alloc_fold byte_rep pa ph h2 st2 y tl)
  = let v = M.field y o 0 in
    fields1 y o;
    fold_alloc ph h st k j v;
    let h' = fh ph h st in
    let c = T.Ok?._0 (fr ph h st) in
    O.some_model_is h' (cabs h');
    let m'' = Some?.v (T.some_model byte_rep h') in
    eliminate exists (m': M.mheap). brepr m' h' /\ fpost ph h st m'
    with begin
      post_k ph h st k m';
      R.heq_sym m' (cabs h'); R.heq_trans m'' (cabs h') m';
      fill_heap h' m'' c v;
      eliminate exists (h3: heap). brepr (M.fill m'' c [v]) h3
      with fold_inner ph h st k j y o tl m' m'' h3
    end
#pop-options

/// **The fold succeeds** while the budget lasts.
#push-options "--fuel 1"
let rec fold_some (ph: T.phase pprog) (h: heap) (st: pst) (k j: nat) (y: M.mheap) (ys: list nat)
  : Lemma (requires cok /\ fs ph h st k j /\ j + L.length ys <= n_pages /\ ynice k y /\
                    (forall (o: nat). L.memP o ys ==> M.is_block y o /\ storable_w (M.field y o 0)))
          (ensures Some? (T.alloc_fold byte_rep pa ph h st y ys))
          (decreases ys)
  = match ys with
    | [] -> ()
    | o :: tl ->
      fold_one ph h st k j y o tl;
      eliminate exists (h2: heap) (st2: pst). fs ph h2 st2 k (j + 1) /\
                  T.alloc_fold byte_rep pa ph h st y (o :: tl) == T.alloc_fold byte_rep pa ph h2 st2 y tl
      with fold_some ph h2 st2 k (j + 1) y tl
#pop-options

/// A list without repeats, of 0 and 2: at most two.
#push-options "--fuel 3"
let short (ys: list nat)
  : Lemma (requires L.noRepeats ys /\ (forall (o: nat). L.memP o ys ==> o == 0 \/ o == 2))
          (ensures L.length ys <= 2)
  = match ys with
    | a :: b :: c :: _ -> ()
    | _ -> ()
#pop-options

/// **`OutOfRoom` is never justified.**
let no_oor (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world) (k j: nat)
  : Lemma (requires cok /\ fs ph cw.T.cmaj st k j /\ j + 2 <= n_pages /\ ynice k w.M.yng /\
                    (forall (o: nat). M.is_block w.M.yng o ==> storable_w (M.field w.M.yng o 0)))
          (ensures ~(T.oor_justified byte_rep pa ph st cw w))
  = let aux (ys: list nat)
      : Lemma (requires L.noRepeats ys /\ (forall (o: nat). L.memP o ys ==> M.is_block w.M.yng o /\ M.minor_live w o))
              (ensures Some? (T.alloc_fold byte_rep pa ph cw.T.cmaj st w.M.yng ys))
      = short ys;
        fold_some ph cw.T.cmaj st k j w.M.yng ys in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// ---------------------------------------------------------------------------
/// The pages it costs
/// ---------------------------------------------------------------------------

/// Distinct entries among two values: at most two.
let two_values (q: seq U64.t) (u1 u2: U64.t)
  : Lemma (requires PR.qdistinct q /\ (forall (i: nat). i < Seq.length q ==> Seq.index q i == u1 \/ Seq.index q i == u2))
          (ensures Seq.length q <= 2)
  = if Seq.length q >= 3 then begin
      assert (Seq.index q 0 == u1 \/ Seq.index q 0 == u2);
      assert (Seq.index q 1 == u1 \/ Seq.index q 1 == u2);
      assert (Seq.index q 2 == u1 \/ Seq.index q 2 == u2)
    end

/// A nursery object of a nice nursery: one of the two, of one field.
let entry_ok (k: nat) (y: M.mheap) (ms: minor_state) (m: U64.t)
  : Lemma (requires Y.yrepr y ms /\ ynice k y /\ Seq.mem m (minor_objects ms))
          (ensures (m == PC.yobj 0 \/ m == PC.yobj 2) /\ minor_wosize ms m == 1)
  = Q.obj_young y ms m;
    PC.young_obj y ms (Q.yof m)

/// The queue's entries: Y1 and Y2, one field each.
let q_entries (#s: Type0) (k: nat) (y: M.mheap) (ms: minor_state) (tl: P.tal s) (g0: heap) (st0: s) (cs: P.gstate s)
  : Lemma (requires Y.yrepr y ms /\ ynice k y /\ PR.qok tl ms g0 st0 cs)
          (ensures Seq.length cs.P.queue <= 2 /\
                   (forall (i: nat). i < Seq.length cs.P.queue ==>
                      minor_wosize ms (Seq.index cs.P.queue i) + 1 <= small_max))
  = smax ();
    let q = cs.P.queue in
    let ent (i: nat) : Lemma (i < Seq.length q ==>
                              (Seq.index q i == PC.yobj 0 \/ Seq.index q i == PC.yobj 2) /\
                              minor_wosize ms (Seq.index q i) + 1 <= small_max)
      = if i < Seq.length q then begin
          assert (PR.qentry tl ms g0 st0 cs i);
          entry_ok k y ms (Seq.index q i)
        end in
    FStar.Classical.forall_intro ent;
    two_values q (PC.yobj 0) (PC.yobj 2)

/// **A minor collection costs at most two pages.**
#push-options "--z3rlimit 40"
let minor_kinds (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world) (k j: nat)
  : Lemma (requires T.cviews byte_rep cw w /\ T.minor_pre pa ph st cw.T.cmaj w /\ PWP.kinds_ok st.ps j /\
                    ynice k w.M.yng)
          (ensures (match pc.n.collect ph st cw with
                    | T.Done _ st' _ _ -> PWP.kinds_ok (st' <: pst).ps (j + 2)
                    | _ -> True))
  = smax ();
    PM.run_done ph st cw w;
    let ms = cw.T.cyng in
    let wc = BM.cview cw in
    let tl = PRe.ptal ph st in
    let g0 = gl cw.T.cmaj st in
    let roots = LV.roots_of wc in
    let cs = P.promote tl ms g0 st.ps roots in
    let q = cs.P.queue in
    q_entries k w.M.yng ms tl g0 st.ps cs;
    PWP.replay_kinds ph st ms g0 q (Seq.length q) j;
    PWP.kinds_mono (snd (PR.replay tl ms g0 st.ps q (Seq.length q))) (j + Seq.length q) (j + 2)
#pop-options
