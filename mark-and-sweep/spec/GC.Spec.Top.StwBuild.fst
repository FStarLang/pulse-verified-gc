/// ---------------------------------------------------------------------------
/// GC.Spec.Top.StwBuild - the stop-the-world cycle exists
/// ---------------------------------------------------------------------------
///
/// Design doc §16.7 (T2, part 1).  From an idle configuration with the run
/// invariant, under the contracts, a whole cycle with no other event runs
/// to its end (`stw_build`): slices of one move while the mark is not done
/// (`pick`: scan the next field, blacken a block with none left, or start
/// a grey block), each strictly decreasing the mark's measure ((6): white,
/// then grey, live objects below `size`, then the fields the scanned block
/// has left, `mm`); then sweep steps while the sweep is not
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
let mid (a: slices) (b: nat) : list event = L.append (L.map ESlice a) (EHandover :: swp b)

let swp_zero () : Lemma (swp 0 == [EEnd]) = ()
let swp_succ (b: nat) : Lemma (swp (b + 1) == ESweep :: swp b) = ()
let mid_zero (b: nat) : Lemma (mid [] b == EHandover :: swp b) = ()
let mid_succ (mvs: list move) (a: slices) (b: nat) : Lemma (mid (mvs :: a) b == ESlice mvs :: mid a b) = ()

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

let rec mid_idx (a: slices) (b k: nat)
  : Lemma (requires k <= L.length a + b + 1)
          (ensures L.length (mid a b) == L.length a + b + 2 /\
                   (k < L.length a + b + 1 ==> coll (L.index (mid a b) k)) /\
                   (k = L.length a + b + 1 ==> L.index (mid a b) k == EEnd))
          (decreases a)
  = match a with
    | [] ->
      mid_zero b;
      if k = 0 then swp_idx b 0 else swp_idx b (k - 1)
    | mvs :: a' ->
      mid_succ mvs a' b;
      if k = 0 then mid_idx a' b 0 else mid_idx a' b (k - 1)

/// **The shape**: start, then collector events, then the end.
let tail_shape (a: slices) (b k: nat)
  : Lemma (requires k <= L.length a + b + 2)
          (ensures L.length (stw_tail a b) == L.length a + b + 3 /\
                   (k = 0 ==> L.index (stw_tail a b) k == EStart) /\
                   (0 < k /\ k < L.length a + b + 2 ==> coll (L.index (stw_tail a b) k)) /\
                   (k = L.length a + b + 2 ==> L.index (stw_tail a b) k == EEnd))
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

/// The mark's: white, then grey, live objects, then the fields the block
/// being scanned has left, lexicographically.
let mm (h: mheap) (sc: scan) (lv: nat -> prop) : GTot nat =
  (cnt (white_live h lv) h.size * (h.size + 1) + cnt (grey_live h lv) h.size) * (h.size + 2) + fleft h sc

let lex (a a' g g' n: nat)
  : Lemma (requires a' < a /\ g' <= n) (ensures a' * (n + 1) + g' < a * (n + 1) + g)
  = ML.lemma_mult_le_right (n + 1) a' (a - 1)

let lex2 (u u' f f' n: nat)
  : Lemma (requires u' < u /\ f' <= n + 1) (ensures u' * (n + 2) + f' < u * (n + 2) + f)
  = ML.lemma_mult_le_right (n + 2) u' (u - 1)

let fleft_bound (h: mheap) (sc: scan)
  : Lemma (requires well_formed h) (ensures fleft h sc <= h.size + 1)
  = match sc with
    | Some (o, i) -> if is_block h o then assert (o + wz_of h o < h.size)
    | None -> ()

let lex3 (w w' g g' f f' n: nat)
  : Lemma (requires g' <= n /\ f' <= n + 1 /\
                    (w' < w \/ (w' == w /\ g' < g) \/ (w' == w /\ g' == g /\ f' < f)))
          (ensures (w' * (n + 1) + g') * (n + 2) + f' < (w * (n + 1) + g) * (n + 2) + f)
  = let u : nat = w * (n + 1) + g in
    let u' : nat = w' * (n + 1) + g' in
    if w' < w then begin lex w w' g g' n; lex2 u u' f f' n end
    else if g' < g then lex2 u u' f f' n
    else ()

/// The counts, from the measure's order on sets.
let mm_counts (h h': mheap) (sc sc': scan) (lv: nat -> prop)
  : Lemma (requires mark_dec h sc h' sc' lv /\ h'.size == h.size)
          (ensures (let n = h.size in
                    let w = cnt (white_live h lv) n in
                    let w' = cnt (white_live h' lv) n in
                    let g = cnt (grey_live h lv) n in
                    let g' = cnt (grey_live h' lv) n in
                    w' < w \/ (w' == w /\ g' < g) \/ (w' == w /\ g' == g /\ fleft h' sc' < fleft h sc)))
  = let n = h.size in
    cnt_le (white_live h lv) (white_live h' lv) n;
    if FStar.IndefiniteDescription.strong_excluded_middle
         (exists (o: nat). white_live h lv o /\ ~(white_live h' lv o)) then
      cnt_lt (white_live h lv) (white_live h' lv) n
    else begin
      cnt_eq (white_live h lv) (white_live h' lv) n;
      cnt_le (grey_live h lv) (grey_live h' lv) n;
      if FStar.IndefiniteDescription.strong_excluded_middle
           (exists (o: nat). grey_live h lv o /\ ~(grey_live h' lv o)) then
        cnt_lt (grey_live h lv) (grey_live h' lv) n
      else
        cnt_eq (grey_live h lv) (grey_live h' lv) n
    end

let mm_dec (h h': mheap) (sc sc': scan) (lv: nat -> prop)
  : Lemma (requires mark_dec h sc h' sc' lv /\ h'.size == h.size /\ well_formed h')
          (ensures mm h' sc' lv < mm h sc lv)
  = let n = h.size in
    cnt_bound (grey_live h' lv) n;
    fleft_bound h' sc';
    mm_counts h h' sc sc' lv;
    lex3 (cnt (white_live h lv) n) (cnt (white_live h' lv) n) (cnt (grey_live h lv) n) (cnt (grey_live h' lv) n)
         (fleft h sc) (fleft h' sc') n

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

let slice_facts (#c: comps) (x: config c) (mvs: list move)
  : Lemma (let x' = step c x (ESlice mvs) in
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

/// A move the model allows while something is grey or being scanned.
let pick (h: mheap) (sc: scan) : GTot move =
  match sc with
  | Some (o, i) -> if i < wz_of h o then MGrey else MBlack o
  | None ->
    if FStar.IndefiniteDescription.strong_excluded_middle (exists (g: nat). is_block h g /\ col_of h g == Grey) then begin
      let g = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun g -> is_block h g /\ col_of h g == Grey) in
      if scannable (tag_of h g) && wz_of h g > 0 then MBegin g else MBlack g
    end else MBlack 0

let pick_move (h: mheap) (sc: scan)
  : Lemma (requires (match sc with
                     | Some (o, i) -> is_block h o /\ col_of h o == Grey /\ scannable (tag_of h o) /\ i <= wz_of h o
                     | None -> ~(no_grey h)))
          (ensures move_ok h sc (pick h sc))
  = match sc with
    | Some _ -> ()
    | None -> assert (exists (g: nat). is_block h g /\ col_of h g == Grey)

let one_ok (h: mheap) (sc: scan) (mv: move)
  : Lemma (requires move_ok h sc mv) (ensures moves_ok h sc [mv])
  = assert_norm (moves_ok h sc [mv] == (move_ok h sc mv && moves_ok (move_heap h sc mv) (move_scan sc mv) []))

let pick_ok (#c: comps) (x: config c)
  : Lemma (requires rinv x /\ Marking? x.ph /\ ~(mark_done (mj x) /\ None? (scan_of x)))
          (ensures move_ok (mj x) (scan_of x) (pick (mj x) (scan_of x)) /\ moves_ok (mj x) (scan_of x) [pick (mj x) (scan_of x)])
  = reveal_opaque (`%r_col) (r_col #c);
    pick_move (mj x) (scan_of x);
    one_ok (mj x) (scan_of x) (pick (mj x) (scan_of x))

/// When the mark is done, nothing is being scanned (the scanned block is grey).
let done_none (#c: comps) (x: config c)
  : Lemma (requires rinv x /\ Marking? x.ph /\ mark_done (mj x)) (ensures None? (scan_of x))
  = reveal_opaque (`%r_col) (r_col #c);
    assert (scan_ok x (mj x));
    match scan_of x with
    | Some (o, _) -> assert (is_block (mj x) o ==> col_of (mj x) o <> Grey)
    | None -> ()

let mark_dec1 (#c: comps) (x: config c) (mvs: list move) (lv: nat -> prop)
  : Lemma (requires Marking? x.ph /\ step_post x (ESlice mvs) (step c x (ESlice mvs)) /\ (forall (o: nat). live x o <==> lv o))
          (ensures mm (mj (step c x (ESlice mvs))) (scan_of (step c x (ESlice mvs))) lv < mm (mj x) (scan_of x) lv /\
                   (forall (o: nat). live (step c x (ESlice mvs)) o <==> lv o))
  = let x' = step c x (ESlice mvs) in
    slice_facts x mvs;
    reveal_opaque (`%r_heap) (r_heap #c);
    assert (mark_dec (mj x) (scan_of x) (mj x') (scan_of x') (live x'));
    assert (mark_dec (mj x) (scan_of x) (mj x') (scan_of x') lv);
    mm_dec (mj x) (mj x') (scan_of x) (scan_of x') lv

let rec mark_build (#c: comps) (sty: style) (x: config c) (lv: nat -> prop) (m: nat)
  : Lemma (requires components_ok c /\ rinv x /\ Marking? x.ph /\ x.stopped == false /\
                    (forall (o: nat). live x o <==> lv o) /\ mm (mj x) (scan_of x) lv <= m)
          (ensures exists (a: slices) (b: nat). tail_ok c sty x (mid a b))
          (decreases m)
  = if FStar.IndefiniteDescription.strong_excluded_middle (mark_done (mj x)) then begin
      done_none x;
      cstep sty x EHandover;
      let x' = step c x EHandover in
      handover_facts x;
      sweep_build sty x' (sm x');
      eliminate exists (b: nat). tail_ok c sty x' (swp b)
      with begin
        mid_zero b;
        tail_cons c sty x EHandover (swp b);
        assert (tail_ok c sty x (mid [] b))
      end
    end else begin
      let mvs = [pick (mj x) (scan_of x)] in
      pick_ok x;
      cstep sty x (ESlice mvs);
      let x' = step c x (ESlice mvs) in
      slice_facts x mvs;
      mark_dec1 x mvs lv;
      mark_build sty x' lv (m - 1);
      eliminate exists (a: slices) (b: nat). tail_ok c sty x' (mid a b)
      with begin
        mid_succ mvs a b;
        tail_cons c sty x (ESlice mvs) (mid a b);
        assert (tail_ok c sty x (mid (mvs :: a) b))
      end
    end

/// **A whole cycle runs from an idle configuration**, with nothing else.
let stw_build (#c: comps) (sty: style) (x: config c)
  : Lemma (requires components_ok c /\ rinv x /\ Idle? x.ph /\ x.stopped == false)
          (ensures exists (a: slices) (b: nat). tail_ok c sty x (stw_tail a b))
  = cstep sty x EStart;
    let x1 = step c x EStart in
    start_facts x;
    mark_build sty x1 (live x1) (mm (mj x1) (scan_of x1) (live x1));
    eliminate exists (a: slices) (b: nat). tail_ok c sty x1 (mid a b)
    with begin
      assert (stw_tail a b == EStart :: mid a b);
      tail_cons c sty x EStart (mid a b);
      assert (tail_ok c sty x (stw_tail a b))
    end
