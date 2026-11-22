/// ---------------------------------------------------------------------------
/// GC.Spec.Top.FFOor - a failed promotion justifies OutOfRoom
/// ---------------------------------------------------------------------------
///
/// When the promotion's allocator refuses a live object after the first `k`
/// promotions of the queue (`PromoteRun.wit`), the contract's `alloc_fold`
/// over those `k` young blocks and the refused one ends in `None`
/// (`fold_none`): at each step the byte heap `alloc_fold` picks represents
/// the replay's reading, so its first-fit heap is the replay's (`Canon.same_gl`),
/// and the first-fit allocator does the same as in the promotion.
/// GC.Spec.Top.PagesOor's statements and proofs, over first-fit.

module GC.Spec.Top.FFOor

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.WriteBodyLemmas
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteRep
open GC.Spec.Top.FFAlloc
open GC.Spec.Top.FFReplay
open GC.Spec.Top.PagesQueue
open GC.Spec.Top.FFQueue
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module P = GC.Spec.Pages.Promote
module PR = GC.Spec.Top.PromoteRun
module PC = GC.Spec.Top.PromoteCopy
module Y = GC.Spec.Top.Young
module C = GC.Spec.Top.Canon

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The young blocks promoted from `j` to `k`, then the refused one.
let rec ys_from (q: seq U64.t) (j k: nat) (x: U64.t) : GTot (list nat) (decreases (if j >= k then 0 else k - j)) =
  if j >= k || j >= Seq.length q then [yof x] else yof (Seq.index q j) :: ys_from q (j + 1) k x

/// The first-fit heap of a byte heap and a free-list head.
let at_replay (ph: T.phase U64.t) (st0: ffst) (h0: heap) (ms: minor_state) (q: seq U64.t) (j: nat)
              (h: heap) (st: ffst) : prop =
  let (g, st') = rstate ph st0 h0 ms q j in gl h st == g /\ st == st'

/// The first-fit allocator on a byte heap is the first-fit allocator on its first-fit heap.
let palloc_gl (ph: T.phase U64.t) (h g: heap) (st: ffst) (sz: M.size_t) (tag: M.tag_t)
  : Lemma (requires gl h st == g /\ st.lo == low g)
          (ensures (let (_, st1, r1) = ffalloc ph h st sz tag in
                    let (g1', st1', r1') = ffalloc ph g st sz tag in
                    st1 == st1' /\ r1 == r1' /\ (T.Ok? r1 ==> ffalloc ph h st sz tag == ffalloc ph g st sz tag)))
  = set_low_self g

/// The last step: the refused object.
#push-options "--z3rlimit 40 --fuel 1"
let fold_last (ph: T.phase U64.t) (st0: ffst) (h0: heap) (y: M.mheap) (ms: minor_state) (q: seq U64.t) (k: nat)
              (x: U64.t) (h: heap) (st: ffst)
  : Lemma (requires at_replay ph st0 h0 ms q k h st /\ Y.yrepr y ms /\ Seq.mem x (minor_objects ms) /\
                    minor_wosize ms x > 0 /\ PR.fails_at (ptal ph st0) ms (gl h0 st0) st0.fp q k x /\
                    k <= Seq.length q)
          (ensures T.alloc_fold byte_rep ffa ph h st y [yof x] == None)
  = obj_young y ms x;
    let o = yof x in
    PC.young_obj y ms o;
    let (g, s) = PR.replay (ptal ph st0) ms (gl h0 st0) st0.fp q k in
    promote_palloc ph st0 ms g s x;
    low_set_low h st.lo;
    assert (st == tst g s);
    assert (minor_wosize ms x == M.wz_of y o /\ mtag ms x == M.tag_of y o);
    palloc_gl ph h g st (M.wz_of y o) (M.tag_of y o);
    let (_, _, r) = ffalloc ph h st (M.wz_of y o) (M.tag_of y o) in
    assert (r == T.NoRoom)
#pop-options

/// `some_model` and `some_heap`, when there is one.
let some_model_is (h: heap) (m: M.mheap)
  : Lemma (requires brepr m h)
          (ensures Some? (T.some_model byte_rep h) /\ brepr (Some?.v (T.some_model byte_rep h)) h)
  = ()

let some_heap_is (m: M.mheap) (h: heap)
  : Lemma (requires brepr m h)
          (ensures Some? (T.some_heap byte_rep m) /\ brepr m (Some?.v (T.some_heap byte_rep m)))
  = ()

/// One allocation and its Fill: `alloc_fold` steps to a byte heap whose
/// first-fit heap is the promotion's.
#push-options "--z3rlimit 40 --fuel 1"
let fold_one (ph: T.phase U64.t) (h: heap) (st: ffst) (y: M.mheap) (o: nat) (tl: list nat)
             (g1: heap) (st1: ffst) (c: nat) (g2: heap)
  : Lemma (requires M.wz_of y o >= 1 /\ M.tag_of y o <> M.infix_tag /\
                    ffalloc ph h st (M.wz_of y o) (M.tag_of y o) == (g1, st1, T.Ok c) /\
                    R.heq (cabs g2) (M.fill (cabs g1) c (M.fields_of y o)) /\
                    M.well_formed (cabs g2) /\ gl g2 st1 == g2)
          (ensures exists (h': heap). gl h' st1 == g2 /\
                     T.alloc_fold byte_rep ffa ph h st y (o :: tl) == T.alloc_fold byte_rep ffa ph h' st1 y tl)
  = some_model_is g1 (cabs g1);
    let m' = Some?.v (T.some_model byte_rep g1) in
    let vs = M.fields_of y o in
    assert (R.heq (M.fill m' c vs) (cabs g2));
    some_heap_is (M.fill m' c vs) g2;
    let h'' = Some?.v (T.some_heap byte_rep (M.fill m' c vs)) in
    assert (R.heq (cabs h'') (cabs g2));
    GC.Spec.Top.PagesInst.wf_heq (cabs g2) (cabs h'');
    C.same_gl h'' g2 st1.lo;
    assert (T.alloc_fold byte_rep ffa ph h st y (o :: tl) == T.alloc_fold byte_rep ffa ph h'' st1 y tl)
#pop-options

/// One promoted object of the queue: `alloc_fold` takes the same step.
#push-options "--z3rlimit 40"
let fold_step (ph: T.phase U64.t) (st0: ffst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state)
              (cs: P.gstate U64.t) (j: nat) (h: heap) (st: ffst) (tl: list nat)
  : Lemma (requires qpre ph st0 h0 y w ms cs /\ j < Seq.length cs.P.queue /\
                    at_replay ph st0 h0 ms cs.P.queue j h st)
          (ensures exists (h': heap) (st': ffst).
                     at_replay ph st0 h0 ms cs.P.queue (j + 1) h' st' /\
                     T.alloc_fold byte_rep ffa ph h st y (yof (Seq.index cs.P.queue j) :: tl) ==
                     T.alloc_fold byte_rep ffa ph h' st' y tl)
  = let q = cs.P.queue in
    ri_queue ph st0 h0 y w ms cs j;
    qpre_elim ph st0 h0 y w ms cs;
    let x = Seq.index q j in
    assert (PR.qentry (ptal ph st0) ms (gl h0 st0) st0.fp cs j);
    obj_young y ms x;
    let o = yof x in
    PC.young_obj y ms o;
    let (g, s) = PR.replay (ptal ph st0) ms (gl h0 st0) st0.fp q j in
    GC.Spec.Top.PagesInst.wf_heq w.M.maj (cabs h0);
    ri_step ph st0 h0 y ms g (tst g s) (cabs g) (copies q cs.P.fwd j) o;
    replay_unfold (ptal ph st0) ms (gl h0 st0) st0.fp q (j + 1);
    let (g2, s2, ob) = PR.promote_at (ptal ph st0) ms g s x in
    let c = maddr ob in
    let wz : M.size_t = M.wz_of y o in
    let tag : M.tag_t = M.tag_of y o in
    let (g1, st1, res) = ffalloc ph g (tst g s) wz tag in
    low_set_low h st.lo;
    palloc_gl ph h g st wz tag;
    ri_elim_wf ph st0 h0 y g2 (tst g2 s2) (cabs g2) ((o, c) :: copies q cs.P.fwd j);
    assert (ffalloc ph h st wz tag == (g1, st1, T.Ok c));
    assert (st1 == tst g2 s2);
    fold_one ph h st y o tl g1 st1 c g2;
    assert (rstate ph st0 h0 ms q (j + 1) == (g2, st1));
    let aux (h': heap)
      : Lemma (requires gl h' st1 == g2 /\
                        T.alloc_fold byte_rep ffa ph h st y (o :: tl) == T.alloc_fold byte_rep ffa ph h' st1 y tl)
              (ensures exists (h': heap) (st': ffst).
                         at_replay ph st0 h0 ms q (j + 1) h' st' /\
                         T.alloc_fold byte_rep ffa ph h st y (yof (Seq.index q j) :: tl) ==
                         T.alloc_fold byte_rep ffa ph h' st' y tl)
      = assert (at_replay ph st0 h0 ms q (j + 1) h' st1) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
#pop-options

/// What the fold needs, sealed.
[@@"opaque_to_smt"]
let fpre (ph: T.phase U64.t) (st0: ffst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state)
         (cs: P.gstate U64.t) (k: nat) (x: U64.t) : prop =
  qpre ph st0 h0 y w ms cs /\ k <= Seq.length cs.P.queue /\
  Seq.mem x (minor_objects ms) /\ minor_wosize ms x > 0 /\
  PR.fails_at (ptal ph st0) ms (gl h0 st0) st0.fp cs.P.queue k x

[@@"opaque_to_smt"]
let at_r (ph: T.phase U64.t) (st0: ffst) (h0: heap) (ms: minor_state) (q: seq U64.t) (j: nat) (h: heap) (st: ffst)
  : prop = at_replay ph st0 h0 ms q j h st

let fold_none_last (ph: T.phase U64.t) (st0: ffst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state)
                   (cs: P.gstate U64.t) (k: nat) (x: U64.t) (h: heap) (st: ffst)
  : Lemma (requires fpre ph st0 h0 y w ms cs k x /\ at_r ph st0 h0 ms cs.P.queue k h st)
          (ensures T.alloc_fold byte_rep ffa ph h st y [yof x] == None)
  = reveal_opaque (`%fpre) (fpre ph st0 h0 y w ms cs k x);
    reveal_opaque (`%at_r) (at_r ph st0 h0 ms cs.P.queue k h st);
    qpre_elim ph st0 h0 y w ms cs;
    fold_last ph st0 h0 y ms cs.P.queue k x h st

let fold_none_step (ph: T.phase U64.t) (st0: ffst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state)
                   (cs: P.gstate U64.t) (j k: nat) (x: U64.t) (h: heap) (st: ffst) (tl: list nat)
  : Lemma (requires fpre ph st0 h0 y w ms cs k x /\ j < k /\ j < Seq.length cs.P.queue /\
                    at_r ph st0 h0 ms cs.P.queue j h st)
          (ensures exists (h': heap) (st': ffst).
                     at_r ph st0 h0 ms cs.P.queue (j + 1) h' st' /\
                     T.alloc_fold byte_rep ffa ph h st y (yof (Seq.index cs.P.queue j) :: tl) ==
                     T.alloc_fold byte_rep ffa ph h' st' y tl)
  = reveal_opaque (`%fpre) (fpre ph st0 h0 y w ms cs k x);
    reveal_opaque (`%at_r) (at_r ph st0 h0 ms cs.P.queue j h st);
    fold_step ph st0 h0 y w ms cs j h st tl;
    let aux (h': heap) (st': ffst)
      : Lemma (at_replay ph st0 h0 ms cs.P.queue (j + 1) h' st' ==> at_r ph st0 h0 ms cs.P.queue (j + 1) h' st')
      = reveal_opaque (`%at_r) (at_r ph st0 h0 ms cs.P.queue (j + 1) h' st') in
    FStar.Classical.forall_intro_2 aux

#push-options "--fuel 1"
let ys_cons (q: seq U64.t) (j k: nat) (x: U64.t)
  : Lemma (requires j < k /\ k <= Seq.length q)
          (ensures ys_from q j k x == yof (Seq.index q j) :: ys_from q (j + 1) k x)
  = ()

let ys_last (q: seq U64.t) (k: nat) (x: U64.t) : Lemma (ys_from q k k x == [yof x]) = ()
#pop-options

let fpre_k (ph: T.phase U64.t) (st0: ffst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state)
           (cs: P.gstate U64.t) (k: nat) (x: U64.t)
  : Lemma (requires fpre ph st0 h0 y w ms cs k x) (ensures k <= Seq.length cs.P.queue)
  = reveal_opaque (`%fpre) (fpre ph st0 h0 y w ms cs k x)

/// **The fold over the promoted objects and the refused one fails.**
let rec fold_none (ph: T.phase U64.t) (st0: ffst) (h0: heap) (y: M.mheap) (w: M.world) (ms: minor_state)
                  (cs: P.gstate U64.t) (j k: nat) (x: U64.t) (h: heap) (st: ffst)
  : Lemma (requires fpre ph st0 h0 y w ms cs k x /\ j <= k /\ at_r ph st0 h0 ms cs.P.queue j h st)
          (ensures T.alloc_fold byte_rep ffa ph h st y (ys_from cs.P.queue j k x) == None)
          (decreases (k - j))
  = fpre_k ph st0 h0 y w ms cs k x;
    if j = k then begin
      ys_last cs.P.queue k x;
      fold_none_last ph st0 h0 y w ms cs k x h st
    end
    else begin
      let tl = ys_from cs.P.queue (j + 1) k x in
      ys_cons cs.P.queue j k x;
      fold_none_step ph st0 h0 y w ms cs j k x h st tl;
      let aux (h': heap) (st': ffst)
        : Lemma (requires at_r ph st0 h0 ms cs.P.queue (j + 1) h' st' /\
                          T.alloc_fold byte_rep ffa ph h st y (yof (Seq.index cs.P.queue j) :: tl) ==
                          T.alloc_fold byte_rep ffa ph h' st' y tl)
                (ensures T.alloc_fold byte_rep ffa ph h st y (ys_from cs.P.queue j k x) == None)
        = fold_none ph st0 h0 y w ms cs (j + 1) k x h' st' in
      FStar.Classical.forall_intro_2 (fun h' st' -> FStar.Classical.move_requires (aux h') st')
    end

/// The start is at the replay of no promotion.
#push-options "--fuel 1"
let at_start (ph: T.phase U64.t) (st0: ffst) (h0: heap) (ms: minor_state) (q: seq U64.t)
  : Lemma (at_r ph st0 h0 ms q 0 h0 st0)
  = reveal_opaque (`%at_r) (at_r ph st0 h0 ms q 0 h0 st0);
    low_set_low h0 st0.lo;
    assert (PR.replay (ptal ph st0) ms (gl h0 st0) st0.fp q 0 == (gl h0 st0, st0.fp))
#pop-options

/// The objects of `ys_from`, each a queued object of the prefix or the refused one.
#push-options "--fuel 2"
let rec ys_mem (q: seq U64.t) (j k: nat) (x: U64.t) (o: nat)
  : Lemma (requires L.memP o (ys_from q j k x))
          (ensures o == yof x \/ (exists (i: nat). j <= i /\ i < k /\ i < Seq.length q /\ o == yof (Seq.index q i)))
          (decreases (if j >= k then 0 else k - j))
  = if j >= k || j >= Seq.length q then ()
    else if o = yof (Seq.index q j) then
      FStar.Classical.exists_intro
        (fun (i: nat) -> j <= i /\ i < k /\ i < Seq.length q /\ o == yof (Seq.index q i)) j
    else ys_mem q (j + 1) k x o
#pop-options

/// Two queued objects with the same young block are the same.
let yof_inj (y: M.mheap) (ms: minor_state) (a b: U64.t)
  : Lemma (requires Y.yrepr y ms /\ Seq.mem a (minor_objects ms) /\ Seq.mem b (minor_objects ms) /\ yof a == yof b)
          (ensures a == b)
  = obj_young y ms a; obj_young y ms b

#push-options "--fuel 2 --z3rlimit 40"
let rec ys_norep (y: M.mheap) (ms: minor_state) (q: seq U64.t) (j k: nat) (x: U64.t)
  : Lemma (requires Y.yrepr y ms /\ PR.qdistinct q /\ k <= Seq.length q /\
                    (forall (i: nat). i < Seq.length q ==> Seq.mem (Seq.index q i) (minor_objects ms)) /\
                    Seq.mem x (minor_objects ms) /\ (forall (i: nat). i < k ==> Seq.index q i =!= x))
          (ensures L.noRepeats (ys_from q j k x))
          (decreases (if j >= k then 0 else k - j))
  = if j >= k then ()
    else begin
      ys_norep y ms q (j + 1) k x;
      let qj = Seq.index q j in
      let nm () : Lemma (~(L.memP (yof qj) (ys_from q (j + 1) k x)))
        = if FStar.IndefiniteDescription.strong_excluded_middle (L.memP (yof qj) (ys_from q (j + 1) k x)) then begin
            ys_mem q (j + 1) k x (yof qj);
            if yof qj = yof x then yof_inj y ms qj x
            else begin
              let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
                        (fun i -> j + 1 <= i /\ i < k /\ i < Seq.length q /\ yof qj == yof (Seq.index q i)) in
              yof_inj y ms qj (Seq.index q i);
              PR.qd_elim q j i
            end
          end in
      nm ()
    end
#pop-options
