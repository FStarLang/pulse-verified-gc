/// ---------------------------------------------------------------------------
/// GC.Spec.Top.StwBuild - the stop-the-world cycle exists
/// ---------------------------------------------------------------------------
///
/// Design doc §16.7 (T2, part 1).  From an idle configuration with the run
/// invariant, under the contracts, a whole cycle with no other event runs
/// to its end (`stw_build`): slices while the mark is not done, each
/// strictly decreasing the mark's measure ((6): white, then grey, live
/// objects below `size`, `mm`); then sweep steps while the sweep is not
/// done, each strictly shrinking the unswept addresses below `size` (`sm`).
/// The heap's size is fixed (`cyc`).  Also the shape of `stw_tail`
/// (`tail_shape`).

module GC.Spec.Top.StwBuild

open GC.Spec.Top.Heap
open GC.Spec.Top.Rep
open GC.Spec.Top.Iface
open GC.Spec.Top.Run
open GC.Spec.Top.RInv
open GC.Spec.Top.StepBase
open GC.Spec.Top.Point
open GC.Spec.Top.Stw
open GC.Spec.Top.RunApp
module L = FStar.List.Tot
module C = FStar.Classical
module ML = FStar.Math.Lemmas

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The shape of the tail
/// ---------------------------------------------------------------------------

let coll (e: event) : bool = ESlice? e || EHandover? e || ESweep? e

let swp (b: nat) : list event = L.append (rep b ESweep) [EEnd]
let mid (a b: nat) : list event = L.append (rep a ESlice) (EHandover :: swp b)

let swp_zero () : Lemma (swp 0 == [EEnd]) = ()
let swp_succ (b: nat) : Lemma (swp (b + 1) == ESweep :: swp b) = ()
let mid_zero (b: nat) : Lemma (mid 0 b == EHandover :: swp b) = ()
let mid_succ (a b: nat) : Lemma (mid (a + 1) b == ESlice :: mid a b) = ()

let rec swp_idx (b k: nat)
  : Lemma (requires k <= b)
          (ensures L.length (swp b) == b + 1 /\ (k < b ==> L.index (swp b) k == ESweep) /\ (k = b ==> L.index (swp b) k == EEnd))
          (decreases b)
  = if b = 0 then begin
      swp_zero ();
      assert_norm (L.length [EEnd] == 1 /\ L.index [EEnd] 0 == EEnd)
    end else begin
      swp_succ (b - 1);
      if k = 0 then swp_idx (b - 1) 0 else swp_idx (b - 1) (k - 1)
    end

let rec mid_idx (a b k: nat)
  : Lemma (requires k <= a + b + 1)
          (ensures L.length (mid a b) == a + b + 2 /\
                   (k < a + b + 1 ==> coll (L.index (mid a b) k)) /\
                   (k = a + b + 1 ==> L.index (mid a b) k == EEnd))
          (decreases a)
  = if a = 0 then begin
      mid_zero b;
      if k = 0 then swp_idx b 0 else swp_idx b (k - 1)
    end else begin
      mid_succ (a - 1) b;
      if k = 0 then mid_idx (a - 1) b 0 else mid_idx (a - 1) b (k - 1)
    end

/// **The shape**: start, then collector events, then the end.
let tail_shape (a b k: nat)
  : Lemma (requires k <= a + b + 2)
          (ensures L.length (stw_tail a b) == a + b + 3 /\
                   (k = 0 ==> L.index (stw_tail a b) k == EStart) /\
                   (0 < k /\ k < a + b + 2 ==> coll (L.index (stw_tail a b) k)) /\
                   (k = a + b + 2 ==> L.index (stw_tail a b) k == EEnd))
  = assert (stw_tail a b == EStart :: mid a b);
    if k = 0 then mid_idx a b 0 else mid_idx a b (k - 1)

/// ---------------------------------------------------------------------------
/// Counting below a bound
/// ---------------------------------------------------------------------------

let rec cnt (p: nat -> prop) (n: nat) : GTot nat (decreases n) =
  if n = 0 then 0
  else cnt p (n - 1) + (if FStar.IndefiniteDescription.strong_excluded_middle (p (n - 1)) then 1 else 0)

let rec cnt_bound (p: nat -> prop) (n: nat) : Lemma (ensures cnt p n <= n) (decreases n)
  = if n = 0 then () else cnt_bound p (n - 1)

let rec cnt_le (p q: nat -> prop) (n: nat)
  : Lemma (requires forall (o: nat). o < n /\ q o ==> p o) (ensures cnt q n <= cnt p n) (decreases n)
  = if n = 0 then () else cnt_le p q (n - 1)

let rec cnt_lt (p q: nat -> prop) (n: nat)
  : Lemma (requires (forall (o: nat). o < n /\ q o ==> p o) /\ (exists (o: nat). o < n /\ p o /\ ~(q o)))
          (ensures cnt q n < cnt p n) (decreases n)
  = if FStar.IndefiniteDescription.strong_excluded_middle (exists (o: nat). o < n - 1 /\ p o /\ ~(q o)) then begin
      cnt_lt p q (n - 1)
    end else
      cnt_le p q (n - 1)

let cnt_eq (p q: nat -> prop) (n: nat)
  : Lemma (requires forall (o: nat). o < n ==> (p o <==> q o)) (ensures cnt q n == cnt p n)
  = cnt_le p q n; cnt_le q p n

/// ---------------------------------------------------------------------------
/// The measures
/// ---------------------------------------------------------------------------

/// The mark's: white, then grey, live objects, lexicographically.
let mm (h: mheap) (lv: nat -> prop) : GTot nat =
  cnt (white_live h lv) h.size * (h.size + 1) + cnt (grey_live h lv) h.size

let lex (a a' g g' n: nat)
  : Lemma (requires a' < a /\ g' <= n) (ensures a' * (n + 1) + g' < a * (n + 1) + g)
  = ML.lemma_mult_le_right (n + 1) a' (a - 1)

let mm_dec (h h': mheap) (lv: nat -> prop)
  : Lemma (requires mark_decreases h h' lv /\ h'.size == h.size) (ensures mm h' lv < mm h lv)
  = let n = h.size in
    cnt_bound (grey_live h' lv) n;
    cnt_le (white_live h lv) (white_live h' lv) n;
    if FStar.IndefiniteDescription.strong_excluded_middle
         (exists (o: nat). white_live h lv o /\ ~(white_live h' lv o)) then begin
      cnt_lt (white_live h lv) (white_live h' lv) n;
      lex (cnt (white_live h lv) n) (cnt (white_live h' lv) n)
          (cnt (grey_live h lv) n) (cnt (grey_live h' lv) n) n
    end else begin
      cnt_eq (white_live h lv) (white_live h' lv) n;
      cnt_lt (grey_live h lv) (grey_live h' lv) n
    end

/// The sweep's: the unswept addresses below `size`.
let uns (k: sweep_kind) (p: k.progress) (o: nat) : prop = k.unswept p o == true

let sm (#c: comps) (x: config c) : GTot nat =
  match x.ph with
  | Sweeping p -> cnt (uns c.k p) (mj x).size
  | _ -> 0

/// ---------------------------------------------------------------------------
/// One collector step
/// ---------------------------------------------------------------------------

let cstep (#c: comps) (sty: style) (x: config c) (e: event)
  : Lemma (requires components_ok c /\ rinv x /\ enabled c x e /\ ~(is_mutator_event e))
          (ensures conds c sty x e /\ step_post x e (step c x e))
  = hyps_of_ok c x e;
    step_ok x e

let slice_facts (#c: comps) (x: config c)
  : Lemma (let x' = step c x ESlice in
           x'.ph == x.ph /\ x'.stopped == x.stopped /\ x'.snap == x.snap /\ x'.allocd == x.allocd)
  = ()

let handover_facts (#c: comps) (x: config c)
  : Lemma (let x' = step c x EHandover in Sweeping? x'.ph /\ x'.stopped == x.stopped)
  = ()

let sweep_facts (#c: comps) (x: config c)
  : Lemma (requires Sweeping? x.ph)
          (ensures (let x' = step c x ESweep in Sweeping? x'.ph /\ x'.stopped == x.stopped))
  = ()

let start_facts (#c: comps) (x: config c)
  : Lemma (let x' = step c x EStart in Marking? x'.ph /\ x'.stopped == x.stopped)
  = ()

/// ---------------------------------------------------------------------------
/// The loops
/// ---------------------------------------------------------------------------

let tail_cons (c: comps) (sty: style) (x: config c) (e: event) (r: list event)
  : Lemma (tail_ok c sty x (e :: r) <==> conds c sty x e /\ tail_ok c sty (step c x e) r)
  = ()

let sweep_dec (#c: comps) (x: config c)
  : Lemma (requires Sweeping? x.ph /\ step_post x ESweep (step c x ESweep))
          (ensures sm (step c x ESweep) < sm x)
  = let x' = step c x ESweep in
    sweep_facts x;
    let Sweeping p = x.ph in
    let Sweeping p' = x'.ph in
    assert ((mj x').size == (mj x).size);
    assert (forall (o: nat). c.k.unswept p' o ==> c.k.unswept p o);
    assert (exists (o: nat). o < (mj x).size /\ region c.k p p' o);
    cnt_lt (uns c.k p) (uns c.k p') (mj x).size

let rec sweep_build (#c: comps) (sty: style) (x: config c) (m: nat)
  : Lemma (requires components_ok c /\ rinv x /\ Sweeping? x.ph /\ x.stopped == false /\ sm x <= m)
          (ensures exists (b: nat). tail_ok c sty x (swp b))
          (decreases m)
  = let Sweeping p = x.ph in
    if c.s.done p then begin
      cstep sty x EEnd;
      swp_zero ();
      tail_cons c sty x EEnd [];
      assert (tail_ok c sty x (swp 0))
    end else begin
      cstep sty x ESweep;
      let x' = step c x ESweep in
      sweep_facts x;
      sweep_dec x;
      sweep_build sty x' (m - 1);
      eliminate exists (b: nat). tail_ok c sty x' (swp b)
      with begin
        swp_succ b;
        tail_cons c sty x ESweep (swp b);
        assert (tail_ok c sty x (swp (b + 1)))
      end
    end

let mark_dec (#c: comps) (x: config c) (lv: nat -> prop)
  : Lemma (requires Marking? x.ph /\ step_post x ESlice (step c x ESlice) /\ (forall (o: nat). live x o <==> lv o))
          (ensures mm (mj (step c x ESlice)) lv < mm (mj x) lv /\
                   (forall (o: nat). live (step c x ESlice) o <==> lv o))
  = let x' = step c x ESlice in
    slice_facts x;
    assert (mark_decreases (mj x) (mj x') (live x'));
    assert (mark_decreases (mj x) (mj x') lv);
    mm_dec (mj x) (mj x') lv

let rec mark_build (#c: comps) (sty: style) (x: config c) (lv: nat -> prop) (m: nat)
  : Lemma (requires components_ok c /\ rinv x /\ Marking? x.ph /\ x.stopped == false /\
                    (forall (o: nat). live x o <==> lv o) /\ mm (mj x) lv <= m)
          (ensures exists (a b: nat). tail_ok c sty x (mid a b))
          (decreases m)
  = if FStar.IndefiniteDescription.strong_excluded_middle (mark_done (mj x)) then begin
      cstep sty x EHandover;
      let x' = step c x EHandover in
      handover_facts x;
      sweep_build sty x' (sm x');
      eliminate exists (b: nat). tail_ok c sty x' (swp b)
      with begin
        mid_zero b;
        tail_cons c sty x EHandover (swp b);
        assert (tail_ok c sty x (mid 0 b))
      end
    end else begin
      cstep sty x ESlice;
      let x' = step c x ESlice in
      slice_facts x;
      mark_dec x lv;
      mark_build sty x' lv (m - 1);
      eliminate exists (a b: nat). tail_ok c sty x' (mid a b)
      with begin
        mid_succ a b;
        tail_cons c sty x ESlice (mid a b);
        assert (tail_ok c sty x (mid (a + 1) b))
      end
    end

/// **A whole cycle runs from an idle configuration**, with nothing else.
let stw_build (#c: comps) (sty: style) (x: config c)
  : Lemma (requires components_ok c /\ rinv x /\ Idle? x.ph /\ x.stopped == false)
          (ensures exists (a b: nat). tail_ok c sty x (stw_tail a b))
  = cstep sty x EStart;
    let x1 = step c x EStart in
    start_facts x;
    mark_build sty x1 (live x1) (mm (mj x1) (live x1));
    eliminate exists (a b: nat). tail_ok c sty x1 (mid a b)
    with begin
      assert (stw_tail a b == EStart :: mid a b);
      tail_cons c sty x EStart (mid a b);
      assert (tail_ok c sty x (stw_tail a b))
    end
