/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesDone - the minor collection of pages: the end of
/// promotion, the blocks in use, the forwarding map
/// ---------------------------------------------------------------------------
///
/// When the promotion refused no live object (`PromoteRun.wit` fails), at
/// the end of promotion the replay invariant holds with the queue's copies
/// (`end_ri`), and:
///   * the blocks in use after the collection are those before and the
///     copies (`done_in_use`);
///   * the forwarding map's young blocks are live blocks of the nursery
///     (`fwd_live`), and two of them have two copies (`fwd_inj`).

module GC.Spec.Top.PagesDone

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Spec.Pages.Inv
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteRep
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.PagesReplay
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module L = FStar.List.Tot
module U64 = FStar.UInt64
module P = GC.Spec.Pages.Promote
module PL = GC.Spec.Pages.Promote.Loop
module PC_ = GC.Spec.Pages.Promote.Collect
module PR = GC.Spec.Top.PromoteRun
module PC = GC.Spec.Top.PromoteCopy
module PU = GC.Spec.Top.PromoteUpdate
module Y = GC.Spec.Top.Young
module Q = GC.Spec.Top.PagesQueue
module O = GC.Spec.Top.PagesOor
module LV = GC.Spec.Top.PagesLive
module BM = GC.Spec.Top.ByteMark
module PM = GC.Spec.Top.PagesMinor
module F = GC.Spec.Top.PagesFwd

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The end of promotion
/// ---------------------------------------------------------------------------

let cs_of (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) : GTot (P.gstate pstate) =
  P.promote (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) st.ps (LV.roots_of (BM.cview cw))

let cps_of (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) : GTot (list (nat & nat)) =
  let cs = cs_of ph st cw in Q.copies cs.P.queue cs.P.fwd (Seq.length cs.P.queue)

/// What the `Done` case starts from.
[@@"opaque_to_smt"]
let dpre (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world) : prop =
  T.cviews byte_rep cw w /\ T.minor_pre pa ph st cw.T.cmaj w /\
  ~(PR.wit (ptal ph st) cw.T.cyng (LV.live (BM.cview cw) cw.T.cyng) (gl cw.T.cmaj st) st.ps (cs_of ph st cw).P.queue)

let dpre_elim (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires dpre ph st cw w)
          (ensures T.cviews byte_rep cw w /\ T.minor_pre pa ph st cw.T.cmaj w /\
                   ~(PR.wit (ptal ph st) cw.T.cyng (LV.live (BM.cview cw) cw.T.cyng) (gl cw.T.cmaj st) st.ps
                       (cs_of ph st cw).P.queue))
  = reveal_opaque (`%dpre) (dpre ph st cw w)

/// The promotion's state at its end.
let end_sok (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires dpre ph st cw w)
          (ensures (let cs = cs_of ph st cw in
                    let roots = LV.roots_of (BM.cview cw) in
                    PR.sok (ptal ph st) cw.T.cyng (LV.live (BM.cview cw) cw.T.cyng) (gl cw.T.cmaj st) st.ps cs /\
                    (forall (i: nat). i < Seq.length roots ==> PR.covered cw.T.cyng cs (Seq.index roots i)) /\
                    PR.scanned cw.T.cyng cs (Seq.length cs.P.queue)))
  = dpre_elim ph st cw w;
    PM.run_done ph st cw w

/// **The replay invariant at the end of promotion.**
#push-options "--z3rlimit 40"
let end_ri (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires dpre ph st cw w)
          (ensures (let cs = cs_of ph st cw in
                    ri ph st cw.T.cmaj w.M.yng cs.P.major (tst cs.P.major cs.P.st) (cabs cs.P.major) (cps_of ph st cw)))
  = end_sok ph st cw w;
    dpre_elim ph st cw w;
    let cs = cs_of ph st cw in
    PM.views cw w;
    PM.qpre_intro ph st cw.T.cmaj w.M.yng w cw.T.cyng cs;
    Q.ri_queue ph st cw.T.cmaj w.M.yng w cw.T.cyng cs (Seq.length cs.P.queue);
    assert (PR.replay (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) st.ps cs.P.queue (Seq.length cs.P.queue) ==
            (cs.P.major, cs.P.st))
#pop-options

/// No two queued objects share a young block.
let end_keys (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires dpre ph st cw w)
          (ensures (let cs = cs_of ph st cw in F.keys_distinct cs.P.queue (Seq.length cs.P.queue)))
  = end_sok ph st cw w;
    dpre_elim ph st cw w;
    PM.views cw w;
    let cs = cs_of ph st cw in
    PM.queue_objs (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) st.ps cs;
    let one (i j: nat)
      : Lemma (i < Seq.length cs.P.queue /\ j < Seq.length cs.P.queue /\
               Q.yof (Seq.index cs.P.queue i) == Q.yof (Seq.index cs.P.queue j) ==> i == j)
      = if i < Seq.length cs.P.queue && j < Seq.length cs.P.queue &&
           Q.yof (Seq.index cs.P.queue i) = Q.yof (Seq.index cs.P.queue j) then begin
          O.yof_inj w.M.yng cw.T.cyng (Seq.index cs.P.queue i) (Seq.index cs.P.queue j);
          PR.qd_elim cs.P.queue i j
        end in
    FStar.Classical.forall_intro_2 one

/// ---------------------------------------------------------------------------
/// The heap after the update
/// ---------------------------------------------------------------------------

let r_of (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) : GTot (P.gresult pstate) =
  P.collect (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) st.ps (LV.roots_of (BM.cview cw))

/// The walk of the promoted heap reaches its end.
let end_walk (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires dpre ph st cw w)
          (ensures (let g = (cs_of ph st cw).P.major in
                    blocks_fit g /\ GC.Spec.Walk.reaches g zero_addr heap_size /\ no_infix_block g /\
                    M.well_formed (cabs g)))
  = end_ri ph st cw w;
    let cs = cs_of ph st cw in
    ri_elim_wf ph st cw.T.cmaj w.M.yng cs.P.major (tst cs.P.major cs.P.st) (cabs cs.P.major) (cps_of ph st cw);
    GC.Spec.Top.PagesAllocOk.inv_walk (iph ph) cs.P.major cs.P.st

/// The reading after the update has the promoted heap's blocks.
let end_hd (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires dpre ph st cw w)
          (ensures (let cs = cs_of ph st cw in
                    let r = r_of ph st cw in
                    r.P.rmajor == update_pointers_with (ptal ph st).P.free cs.P.major cs.P.fwd /\
                    r.P.rst == cs.P.st /\ r.P.rfwd == cs.P.fwd /\
                    (forall (j: nat). (cabs r.P.rmajor).M.hd j == (cabs cs.P.major).M.hd j) /\
                    (forall (w': nat). is_fw r.P.rmajor w' == is_fw cs.P.major w')))
  = end_walk ph st cw w;
    let cs = cs_of ph st cw in
    PU.upd_hd (ptal ph st).P.free cs.P.major cs.P.fwd

/// The pages' blocks in use, through equal headers.
let in_use_hd (st st': pst) (g g': heap) (m m': M.mheap) (x: nat)
  : Lemma (requires (forall (j: nat). m'.M.hd j == m.M.hd j) /\ m'.M.size == m.M.size /\
                    (cabs g').M.hd x == (cabs g).M.hd x)
          (ensures T.in_use pa st' g' m' x == T.in_use pa st g m x)
  = ()

/// The copies are the forwarding map's values.
let mem_fwd (q: seq U64.t) (fwd: forwarding_map) (x: nat)
  : Lemma (requires F.keys_distinct q (Seq.length q))
          (ensures (exists (o: nat). L.memP (o, x) (Q.copies q fwd (Seq.length q))) <==>
                   (exists (o: nat). F.fwd_of (Q.copies q fwd (Seq.length q)) o == Some x))
  = let n = Seq.length q in
    let a (o: nat) : Lemma (L.memP (o, x) (Q.copies q fwd n) ==> F.fwd_of (Q.copies q fwd n) o == Some x)
      = if FStar.IndefiniteDescription.strong_excluded_middle (L.memP (o, x) (Q.copies q fwd n)) then begin
          F.mem_some q fwd n o x;
          let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
                    (fun i -> i < n /\ i < Seq.length q /\ o == Q.yof (Seq.index q i) /\
                              x == maddr (fwd (Seq.index q i))) in
          F.fwd_queue q fwd n i
        end in
    FStar.Classical.forall_intro a;
    let b (o: nat) : Lemma (F.fwd_of (Q.copies q fwd n) o == Some x ==> L.memP (o, x) (Q.copies q fwd n))
      = if F.fwd_of (Q.copies q fwd n) o = Some x then F.some_mem (Q.copies q fwd n) o x in
    FStar.Classical.forall_intro b

/// **The blocks in use after**: those before, and the copies.
#push-options "--z3rlimit 40"
let done_in_use (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires dpre ph st cw w)
          (ensures (let r = r_of ph st cw in
                    let fwd = F.fwd_of (cps_of ph st cw) in
                    forall (x: nat). T.in_use pa (tst r.P.rmajor r.P.rst) r.P.rmajor (cabs r.P.rmajor) x <==>
                      (T.in_use pa st cw.T.cmaj w.M.maj x \/ (exists (o: nat). fwd o == Some x))))
  = let cs = cs_of ph st cw in
    let r = r_of ph st cw in
    dpre_elim ph st cw w;
    end_ri ph st cw w;
    end_hd ph st cw w;
    end_keys ph st cw w;
    ri_iu_def st cw.T.cmaj cs.P.major (tst cs.P.major cs.P.st) (cabs cs.P.major) (cps_of ph st cw);
    let one (x: nat)
      : Lemma (T.in_use pa (tst r.P.rmajor r.P.rst) r.P.rmajor (cabs r.P.rmajor) x ==
               T.in_use pa (tst cs.P.major cs.P.st) cs.P.major (cabs cs.P.major) x /\
               T.in_use pa st cw.T.cmaj (cabs cw.T.cmaj) x == T.in_use pa st cw.T.cmaj w.M.maj x)
      = in_use_hd (tst cs.P.major cs.P.st) (tst r.P.rmajor r.P.rst) cs.P.major r.P.rmajor
          (cabs cs.P.major) (cabs r.P.rmajor) x in
    FStar.Classical.forall_intro one;
    FStar.Classical.forall_intro (mem_fwd cs.P.queue cs.P.fwd)
#pop-options

/// ---------------------------------------------------------------------------
/// The forwarding map: exactly the live young blocks, each once
/// ---------------------------------------------------------------------------

/// **A forwarded young block is live.**
let fwd_live (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world) (o c: nat)
  : Lemma (requires dpre ph st cw w /\ F.fwd_of (cps_of ph st cw) o == Some c)
          (ensures M.is_block w.M.yng o /\ M.minor_live w o)
  = let cs = cs_of ph st cw in
    let n = Seq.length cs.P.queue in
    end_sok ph st cw w;
    dpre_elim ph st cw w;
    PM.views cw w;
    F.fwd_some cs.P.queue cs.P.fwd n o c;
    let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun i -> i < n /\ i < Seq.length cs.P.queue /\ o == Q.yof (Seq.index cs.P.queue i) /\
                        c == maddr (cs.P.fwd (Seq.index cs.P.queue i))) in
    assert (LV.live (BM.cview cw) cw.T.cyng (Seq.index cs.P.queue i));
    PM.queue_objs (ptal ph st) cw.T.cyng (gl cw.T.cmaj st) st.ps cs;
    Q.obj_young w.M.yng cw.T.cyng (Seq.index cs.P.queue i);
    PM.live_heq (BM.cview cw) w o

/// **Two young blocks have two copies.**
let fwd_inj (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world) (o1 o2 c: nat)
  : Lemma (requires dpre ph st cw w /\ F.fwd_of (cps_of ph st cw) o1 == Some c /\
                    F.fwd_of (cps_of ph st cw) o2 == Some c)
          (ensures o1 == o2)
  = let cs = cs_of ph st cw in
    end_ri ph st cw w;
    F.some_mem (cps_of ph st cw) o1 c;
    F.some_mem (cps_of ph st cw) o2 c;
    ri_copies_def ph st cw.T.cmaj w.M.yng (cabs cs.P.major) (cps_of ph st cw)

/// A pointer the nursery resolves leaves room for its object.
let res_bound (y: M.mheap) (a o: nat)
  : Lemma (requires M.young_ok y /\ M.resolve y a == Some o /\ y.M.size == ywords)
          (ensures 8 * a + 16 <= minor_heap_size)
  = assert_norm (minor_heap_size % 8 == 0)

#push-options "--fuel 1"
let rec yroots_mem (y: M.mheap) (rs: list M.value) (a: nat)
  : Lemma (requires L.memP (M.VPtr (M.Young a)) rs /\ Some? (M.resolve y a) /\ 8 * a + 16 <= minor_heap_size)
          (ensures (Y.msz (); Seq.mem (U64.uint_to_t (8 * a + 8)) (LV.yroots y rs)))
  = Y.msz ();
    match rs with
    | v :: tl ->
      FStar.Seq.Properties.lemma_mem_append (LV.yword y v) (LV.yroots y tl);
      if v = M.VPtr (M.Young a) then LV.mem_one (U64.uint_to_t (8 * a + 8)) (U64.uint_to_t (8 * a + 8))
      else yroots_mem y tl a

let rec yrem_mem (m y: M.mheap) (rem: list M.slot) (x i a: nat)
  : Lemma (requires L.memP (x, i) rem /\ M.ptr_field m x i /\ M.field m x i == M.VPtr (M.Young a) /\
                    Some? (M.resolve y a) /\ 8 * a + 16 <= minor_heap_size)
          (ensures (Y.msz (); Seq.mem (U64.uint_to_t (8 * a + 8)) (LV.yrem m y rem)))
  = Y.msz ();
    match rem with
    | (x', i') :: tl ->
      let hd = if M.ptr_field m x' i' then LV.yword y (M.field m x' i') else Seq.empty in
      FStar.Seq.Properties.lemma_mem_append hd (LV.yrem m y tl);
      if (x', i') = (x, i) then LV.mem_one (U64.uint_to_t (8 * a + 8)) (U64.uint_to_t (8 * a + 8))
      else yrem_mem m y tl x i a
#pop-options

/// A covered young pointer's block is forwarded.
#push-options "--z3rlimit 40"
let cov_fwd (y: M.mheap) (ms: minor_state) (cs: P.gstate pstate) (a o: nat)
  : Lemma (requires Y.yrepr y ms /\ M.young_ok y /\ y.M.size == ywords /\ M.resolve y a == Some o /\
                    8 * a + 16 <= minor_heap_size /\ (Y.msz (); PR.covered ms cs (U64.uint_to_t (8 * a + 8))))
          (ensures 8 * o + 8 < pow2 64 /\ cs.P.fwd (PC.yobj o) <> 0UL /\ M.is_block y o)
  = Y.msz ();
    LV.a1_lt a;
    Y.young_resolve y ms a o;
    GC.Spec.Top.ToyMark.resolve_resolves y a o;
    PC.young_obj y ms o;
    PR.covered_def ms cs (U64.uint_to_t (8 * a + 8))
#pop-options

/// A root word is covered.
let root_covered (ms: minor_state) (cs: P.gstate pstate) (roots: seq U64.t) (u: U64.t)
  : Lemma (requires (forall (i: nat). i < Seq.length roots ==> PR.covered ms cs (Seq.index roots i)) /\ Seq.mem u roots)
          (ensures PR.covered ms cs u)
  = FStar.Seq.Properties.mem_index u roots

let root_cov_at (ms: minor_state) (cs: P.gstate pstate) (roots: seq U64.t) (a: nat)
  : Lemma (requires (forall (i: nat). i < Seq.length roots ==> PR.covered ms cs (Seq.index roots i)) /\
                    8 * a + 16 <= minor_heap_size /\ (Y.msz (); Seq.mem (U64.uint_to_t (8 * a + 8)) roots))
          (ensures (Y.msz (); PR.covered ms cs (U64.uint_to_t (8 * a + 8))))
  = Y.msz ();
    root_covered ms cs roots (U64.uint_to_t (8 * a + 8))

/// A field of a scanned queued object, its young pointer covered.
#push-options "--z3rlimit 40"
let field_cov (y: M.mheap) (ms: minor_state) (cs: P.gstate pstate) (j: nat) (o i a: nat)
  : Lemma (requires Y.yrepr y ms /\ PR.scanned ms cs (Seq.length cs.P.queue) /\ j < Seq.length cs.P.queue /\
                    M.is_block y o /\ 8 * o + 8 < pow2 64 /\ Seq.index cs.P.queue j == PC.yobj o /\
                    M.ptr_field y o i /\ M.field y o i == M.VPtr (M.Young a))
          (ensures 8 * a + 16 <= minor_heap_size /\ (Y.msz (); PR.covered ms cs (U64.uint_to_t (8 * a + 8))))
  = Y.msz ();
    PC.young_obj y ms o;
    minor_scan_wosize_cases ms (PC.yobj o);
    PR.nsc_def ms (PC.yobj o);
    assert (i < PR.nsc ms (PC.yobj o));
    PR.fld_def ms (PC.yobj o) i;
    let f = minor_read_field ms (PC.yobj o) i in
    LV.tmo_id f;
    PC.young_field y ms o i;
    absv_young f a;
    U64.v_inj f (U64.uint_to_t (8 * a + 8));
    assert (PR.covered ms cs (PR.fld ms (PC.yobj o) i))
#pop-options

/// What the induction carries: the closure of the end of promotion.
[@@"opaque_to_smt"]
let closure (cw: T.cworld heap minor_state) (cs: P.gstate pstate) (live: U64.t -> prop) (g0: heap) (s0: pstate)
            (a: P.tal pstate) : prop =
  let wc = BM.cview cw in
  let ms = cw.T.cyng in
  Y.yrepr wc.M.yng ms /\ M.young_ok wc.M.yng /\ wc.M.yng.M.size == ywords /\
  (forall (i: nat). i < Seq.length (LV.roots_of wc) ==> PR.covered ms cs (Seq.index (LV.roots_of wc) i)) /\
  PR.scanned ms cs (Seq.length cs.P.queue) /\ PR.qok a ms g0 s0 cs

/// **Every traced young block is forwarded.**
#push-options "--z3rlimit 40"
let rec live_fwd (cw: T.cworld heap minor_state) (cs: P.gstate pstate) (live: U64.t -> prop) (g0: heap)
                 (s0: pstate) (a: P.tal pstate) (o: nat) (l: M.mlive (BM.cview cw) o)
  : Lemma (requires closure cw cs live g0 s0 a)
          (ensures 8 * o + 8 < pow2 64 /\ cs.P.fwd (PC.yobj o) <> 0UL /\ M.is_block (BM.cview cw).M.yng o)
          (decreases l)
  = let wc = BM.cview cw in
    let ms = cw.T.cyng in
    let y = wc.M.yng in
    reveal_opaque (`%closure) (closure cw cs live g0 s0 a);
    Y.msz ();
    match l with
    | M.LRoot _ a' _ ->
      res_bound y a' o;
      yroots_mem y wc.M.roots a';
      FStar.Seq.Properties.lemma_mem_append (LV.yroots y wc.M.roots) (LV.yrem wc.M.maj y wc.M.rem);
      root_cov_at ms cs (LV.roots_of wc) a';
      cov_fwd y ms cs a' o
    | M.LRem _ x i a' _ ->
      res_bound y a' o;
      yrem_mem wc.M.maj y wc.M.rem x i a';
      FStar.Seq.Properties.lemma_mem_append (LV.yroots y wc.M.roots) (LV.yrem wc.M.maj y wc.M.rem);
      root_cov_at ms cs (LV.roots_of wc) a';
      cov_fwd y ms cs a' o
    | M.LStep p _ l' _ ->
      live_fwd cw cs live g0 s0 a p l';
      PC.young_obj y ms p;
      assert (~(is_infix_in_minor ms (PC.yobj p)));
      assert (Seq.mem (PC.yobj p) cs.P.queue);
      let j = FStar.Seq.Properties.index_mem (PC.yobj p) cs.P.queue in
      let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun i -> exists (a': nat). M.ptr_field y p i /\ M.field y p i == M.VPtr (M.Young a') /\
                                       M.resolve y a' == Some o) in
      let a' = FStar.IndefiniteDescription.indefinite_description_ghost nat
                 (fun a' -> M.ptr_field y p i /\ M.field y p i == M.VPtr (M.Young a') /\ M.resolve y a' == Some o) in
      field_cov y ms cs j p i a';
      cov_fwd y ms cs a' o
#pop-options

let closure_intro (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world)
  : Lemma (requires dpre ph st cw w)
          (ensures (let cs = cs_of ph st cw in
                    closure cw cs (LV.live (BM.cview cw) cw.T.cyng) (gl cw.T.cmaj st) st.ps (ptal ph st)))
  = let cs = cs_of ph st cw in
    end_sok ph st cw w;
    dpre_elim ph st cw w;
    PM.views cw w;
    PM.young_ok_heq w.M.yng (BM.cview cw).M.yng;
    reveal_opaque (`%closure) (closure cw cs (LV.live (BM.cview cw) cw.T.cyng) (gl cw.T.cmaj st) st.ps (ptal ph st))

/// **Every live young block is forwarded.**
#push-options "--z3rlimit 40"
let fwd_complete (ph: T.phase pprog) (st: pst) (cw: T.cworld heap minor_state) (w: M.world) (o: nat)
  : Lemma (requires dpre ph st cw w /\ M.is_block w.M.yng o /\ M.minor_live w o)
          (ensures Some? (F.fwd_of (cps_of ph st cw) o))
  = let cs = cs_of ph st cw in
    let wc = BM.cview cw in
    closure_intro ph st cw w;
    dpre_elim ph st cw w;
    PM.views cw w;
    PM.live_heq w wc o;
    let l = FStar.IndefiniteDescription.indefinite_description_ghost (M.mlive wc o) (fun _ -> True) in
    live_fwd cw cs (LV.live wc cw.T.cyng) (gl cw.T.cmaj st) st.ps (ptal ph st) o l;
    end_sok ph st cw w;
    Y.yrepr_elim wc.M.yng cw.T.cyng;
    PC.young_obj wc.M.yng cw.T.cyng o;
    assert (Seq.mem (PC.yobj o) cs.P.queue);
    let i = FStar.Seq.Properties.index_mem (PC.yobj o) cs.P.queue in
    end_keys ph st cw w;
    F.fwd_queue cs.P.queue cs.P.fwd (Seq.length cs.P.queue) i;
    LV.yof_v o
#pop-options
