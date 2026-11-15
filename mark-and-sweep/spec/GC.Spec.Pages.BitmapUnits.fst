/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.BitmapUnits - sweeping a unit with the marks in the bitmap
/// ---------------------------------------------------------------------------
///
/// The real heap `g` has white and blue headers only; the marks are bits of
/// `bs`.  The specification sweeps `with_marks g bs`.  This module says what
/// the marks must look like in a unit (`unit_marks`) for a sweep that reads
/// the bits to compute exactly the specification's sweep, and gives the
/// steps of the two Pulse unit sweeps:
///
///   - **A pool page** is swept as the prototype does: a slot is live when
///     its header's bit is set, a live slot is not written at all, and the
///     page's bitmap words are zeroed at the end.  While the pass is at slot
///     `k`, the real heap with the marks *outside* the slots already passed
///     (`Bitmap.win`) is the specification's heap after those slots
///     (`win_live`, `win_dead`, `win_end`).  It needs the marks of the page
///     to lie on slot headers of white blocks, and no unmarked slot header
///     to be black (`pool_marks`).
///   - **A run** first has its marks made into black headers, one walk step
///     at a time, each bit cleared as its header is written (`mat_step`); the
///     run is then exactly the specification's (`mat_done`), and the
///     header-colour run sweep applies (`run_sim`).  It needs the marks of
///     the run to lie on the run's walk (`run_marks`).

module GC.Spec.Pages.BitmapUnits

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Bitmap

module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Seq = FStar.Seq
module HE = GC.Gen.HeapExtensional
module PI = GC.Spec.Pages.PoolInit
module SP = GC.Spec.Pages.SweepPage
module SR = GC.Spec.Pages.SweepRun
module SO = GC.Spec.Pages.SweepOrder
module IN = GC.Spec.Pages.Init
module RL = GC.Spec.Pages.RunList

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Heaps
/// ---------------------------------------------------------------------------

let write_same (g: heap) (a: hp_addr)
  : Lemma (write_word g a (read_word g a) == g)
  = let aux (x: nat) : Lemma (x < heap_size /\ x % 8 == 0 ==>
                              read_word (write_word g a (read_word g a)) (U64.uint_to_t x) == read_word g (U64.uint_to_t x))
      = if x < heap_size && x % 8 = 0 then rw g a (U64.uint_to_t x) (read_word g a)
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext (write_word g a (read_word g a)) g

let write_write (g: heap) (a: hp_addr) (u v: U64.t)
  : Lemma (write_word (write_word g a u) a v == write_word g a v)
  = let aux (x: nat) : Lemma (x < heap_size /\ x % 8 == 0 ==>
                              read_word (write_word (write_word g a u) a v) (U64.uint_to_t x) ==
                              read_word (write_word g a v) (U64.uint_to_t x))
      = if x < heap_size && x % 8 = 0 then begin
          rw (write_word g a u) a (U64.uint_to_t x) v;
          rw g a (U64.uint_to_t x) u;
          rw g a (U64.uint_to_t x) v
        end
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext (write_word (write_word g a u) a v) (write_word g a v)

let hdr_word (g: heap) (a: hp_addr) : Lemma (hdr g (U64.v a) == read_word g a) = ()

/// ---------------------------------------------------------------------------
/// A pool page
/// ---------------------------------------------------------------------------

/// The marks of pool page `i` of class `c` lie on slot headers of white
/// blocks, and no unmarked slot header is black.
let pool_marks (g: heap) (bs: Seq.seq U32.t) (i: nat) (c: nat{c < n_cls}) : prop =
  (forall (x: nat). page_base i <= x /\ x < page_base (i + 1) /\ marked bs x ==>
     (exists (k: nat). k < n_slots c /\ x == slot_base i c k)) /\
  (forall (k: nat). k < n_slots c ==>
     (marked bs (slot_base i c k) ==> color_at g (slot_base i c k) == White) /\
     (~(marked bs (slot_base i c k)) ==> ~(color_at g (slot_base i c k) == Black)))

let slot_lt (i: nat) (c: nat{c < n_cls}) (j k: nat)
  : Lemma (requires j < k) (ensures slot_base i c j + cls c * 8 <= slot_base i c k)
  = cls_bounds c;
    FStar.Math.Lemmas.lemma_mult_le_right (cls c * 8) (j + 1) k;
    FStar.Math.Lemmas.paren_mul_right j (cls c) 8;
    FStar.Math.Lemmas.paren_mul_right k (cls c) 8

/// A mark between slot `k`'s start and slot `k + 1`'s is slot `k`'s header.
let slot_only (g: heap) (bs: Seq.seq U32.t) (i: nat) (c: nat{c < n_cls}) (k: nat) (x: nat)
  : Lemma (requires pool_marks g bs i c /\ k < n_slots c /\ slot_base i c k <= x /\
                    x < slot_base i c (k + 1) /\ marked bs x)
          (ensures x == slot_base i c k)
  = slot_in_page i c k;
    slots_fill_page i c;
    slot_base_succ i c k;
    eliminate exists (k': nat). k' < n_slots c /\ x == slot_base i c k'
    with begin
      if k' < k then slot_lt i c k' k
      else if k' > k then slot_lt i c k k'
    end

/// No mark lies past the last slot.
let tail_unmarked (g: heap) (bs: Seq.seq U32.t) (i: nat) (c: nat{c < n_cls}) (x: nat)
  : Lemma (requires pool_marks g bs i c /\ slots_end i c <= x /\ x < page_base (i + 1))
          (ensures not (marked bs x))
  = slots_fill_page i c;
    if marked bs x then
      eliminate exists (k: nat). k < n_slots c /\ x == slot_base i c k
      with slot_in_page i c k

/// A slot is live in the specification's heap exactly when its header is
/// marked.
let live_iff (g: heap) (bs: Seq.seq U32.t) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (requires pool_marks g bs i c)
          (ensures SP.live (with_marks g bs) i c k == marked bs (slot_base i c k))
  = let a = PI.slot_hd i c k in
    wm_read g (marked bs) a;
    black_black (read_word g a)

/// The marks outside `[page_base i, x)`.
let wpage (bs: Seq.seq U32.t) (i: nat) (x: nat) : nat -> bool = win bs (page_base i) x

/// Before slot `k`, the passed slots' marks are left out.
let win_slot (bs: Seq.seq U32.t) (i: nat) (c: nat{c < n_cls}) (k: nat) : nat -> bool = wpage bs i (slot_base i c k)

/// **A live slot**: its mark leaves the window, and the specification makes
/// its header white again.
let win_live (g0 s: heap) (bs: Seq.seq U32.t) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (requires pool_marks g0 bs i c /\ marked bs (slot_base i c k) /\
                    read_word s (PI.slot_hd i c k) == read_word g0 (PI.slot_hd i c k))
          (ensures (let a = PI.slot_hd i c k in
                    wm s (win_slot bs i c (k + 1)) ==
                    write_word (wm s (win_slot bs i c k)) a (colorHeader (read_word (with_marks g0 bs) a) White)))
  = let a = PI.slot_hd i c k in
    PI.slot_fits i c k;
    slot_base_succ i c k;
    cls_bounds c;
    wm_read g0 (marked bs) a;
    whiten_black (read_word g0 a);
    let m1 = win_slot bs i c k in
    let m2 = win_slot bs i c (k + 1) in
    let same (x: hp_addr) : Lemma (x <> a ==> m1 (U64.v x) == m2 (U64.v x))
      = if x <> a && slot_base i c k <= U64.v x && U64.v x < slot_base i c (k + 1) && marked bs (U64.v x)
        then slot_only g0 bs i c k (U64.v x)
    in
    FStar.Classical.forall_intro same;
    wm_unmark s m1 m2 a;
    write_write (wm s m2) a (colorHeader (read_word s a) Black) (read_word s a);
    wm_read s m2 a;
    write_same (wm s m2) a

/// **A dead slot**: the window moves past it without changing the heap.
let win_dead (g0 s: heap) (bs: Seq.seq U32.t) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (requires pool_marks g0 bs i c /\ not (marked bs (slot_base i c k)))
          (ensures wm s (win_slot bs i c (k + 1)) == wm s (win_slot bs i c k))
  = slot_base_succ i c k;
    cls_bounds c;
    let same (x: hp_addr) : Lemma (win_slot bs i c k (U64.v x) == win_slot bs i c (k + 1) (U64.v x))
      = if slot_base i c k <= U64.v x && U64.v x < slot_base i c (k + 1) && marked bs (U64.v x)
        then slot_only g0 bs i c k (U64.v x)
    in
    FStar.Classical.forall_intro same;
    wm_ext s (win_slot bs i c k) (win_slot bs i c (k + 1))

/// A slot's link field is not marked.
let link_unmarked (g0: heap) (bs: Seq.seq U32.t) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (requires pool_marks g0 bs i c)
          (ensures not (marked bs (slot_base i c k + 8)))
  = slot_base_succ i c k;
    cls_bounds c;
    PI.slot_fits i c k;
    slot_in_page i c k;
    slots_fill_page i c;
    if marked bs (slot_base i c k + 8) then slot_only g0 bs i c k (slot_base i c k + 8)

/// **The end of the pass**: zeroing the page's bitmap words leaves out the
/// same marks as the window over all the slots.
let win_end (g0 s: heap) (bs: Seq.seq U32.t) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires pool_marks g0 bs i c)
          (ensures wm s (win_slot bs i c (n_slots c)) == with_marks s (zero_page bs i))
  = slots_fill_page i c;
    let same (x: hp_addr) : Lemma (win_slot bs i c (n_slots c) (U64.v x) == marked (zero_page bs i) (U64.v x))
      = zero_page_marked bs i (U64.v x);
        if slots_end i c <= U64.v x && U64.v x < page_base (i + 1) then tail_unmarked g0 bs i c (U64.v x)
    in
    FStar.Classical.forall_intro same;
    wm_ext s (win_slot bs i c (n_slots c)) (marked (zero_page bs i))

/// The window before the first slot leaves nothing out.
let win_start (s: heap) (bs: Seq.seq U32.t) (i: nat) (c: nat{c < n_cls})
  : Lemma (wm s (win_slot bs i c 0) == with_marks s bs)
  = let same (x: hp_addr) : Lemma (win_slot bs i c 0 (U64.v x) == marked bs (U64.v x)) = () in
    FStar.Classical.forall_intro same;
    wm_ext s (win_slot bs i c 0) (marked bs)

/// **A page with no live slot has no mark**, so its bitmap words are zero
/// already.
let freed_unmarked (g0: heap) (bs: Seq.seq U32.t) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires pool_marks g0 bs i c /\ Seq.length bs == bm_len /\
                    not (SP.any_live (with_marks g0 bs) i c (n_slots c)))
          (ensures zero_page bs i == bs)
  = SP.any_live_spec (with_marks g0 bs) i c (n_slots c);
    let none (x: nat) : Lemma (page_base i <= x /\ x < page_base (i + 1) ==> not (marked bs x))
      = if page_base i <= x && x < page_base (i + 1) && marked bs x then
          eliminate exists (k: nat). k < n_slots c /\ x == slot_base i c k
          with live_iff g0 bs i c k
    in
    FStar.Classical.forall_intro none;
    page_words_zero bs i

/// ---------------------------------------------------------------------------
/// A run
/// ---------------------------------------------------------------------------

/// `x` starts a block of the walk from `a` that stops before `e`, as
/// `RunList.olds` walks a run.
#push-options "--fuel 1"
let rec on_walk (g: heap) (a e: nat) (x: nat) : Tot bool (decreases (if a < e then e - a else 0)) =
  if a >= e then false
  else begin
    let w = words_at g a in
    if a + w * 8 > e then false else (x = a || on_walk g (a + w * 8) e x)
  end

let on_walk_step (g: heap) (a e: nat) (x: nat)
  : Lemma (on_walk g a e x ==
           (a < e && a + words_at g a * 8 <= e && (x = a || on_walk g (a + words_at g a * 8) e x)))
  = ()

let rec on_walk_ge (g: heap) (a e: nat) (x: nat)
  : Lemma (requires on_walk g a e x) (ensures a <= x /\ x < e)
          (decreases (if a < e then e - a else 0))
  = if x <> a then on_walk_ge g (a + words_at g a * 8) e x

/// The walk reads only the words from where it starts.
let rec on_walk_local (g1 g2: heap) (lo a e: nat) (x: nat)
  : Lemma (requires SO.hagree g1 g2 lo e /\ lo <= a)
          (ensures on_walk g1 a e x == on_walk g2 a e x)
          (decreases (if a < e then e - a else 0))
  = if a < e then begin
      SO.hdr_agree g1 g2 lo e a;
      let w = words_at g1 a in
      if a + w * 8 <= e then on_walk_local g1 g2 lo (a + w * 8) e x
    end
#pop-options

/// The marks of the run of `n` pages at page `h` lie on its walk.
let run_marks (g: heap) (bs: Seq.seq U32.t) (h: nat) (n: pos) : prop =
  forall (x: nat). page_base h <= x /\ x < page_base (h + n) /\ marked bs x ==>
    on_walk g (page_base h) (page_base (h + n)) x

/// The state of the pass that makes the run's marks black headers, at `cur`:
/// the real heap `r` and the bitmap `b` stand for `w`, the marks before
/// `cur` are cleared, and those after it lie on the walk from it.
let mat_inv (w r: heap) (b: Seq.seq U32.t) (s cur e: nat) : prop =
  with_marks r b == w /\ s <= cur /\
  (forall (x: nat). s <= x /\ x < cur ==> not (marked b x)) /\
  (forall (x: nat). cur <= x /\ x < e /\ marked b x ==> on_walk r cur e x)

let mat_start (w r: heap) (b: Seq.seq U32.t) (h: nat) (n: pos)
  : Lemma (requires with_marks r b == w /\ run_marks r b h n)
          (ensures mat_inv w r b (page_base h) (page_base h) (page_base (h + n)))
  = ()

let one_block (r: heap) (b: Seq.seq U32.t) (cur e: nat) (x: nat)
  : Lemma (requires cur < x /\ x < cur + words_at r cur * 8 /\ (marked b x ==> on_walk r cur e x))
          (ensures not (marked b x))
  = on_walk_step r cur e x;
    if marked b x then on_walk_ge r (cur + words_at r cur * 8) e x

let blacken_agree (r: heap) (a: hp_addr)
  : Lemma (SO.hagree (write_word r a (colorHeader (read_word r a) Black)) r (U64.v a + 8) heap_size)
  = let aux (y: hp_addr) : Lemma (U64.v a + 8 <= U64.v y ==>
                                  read_word (write_word r a (colorHeader (read_word r a) Black)) y == read_word r y)
      = rw r a y (colorHeader (read_word r a) Black)
    in
    FStar.Classical.forall_intro aux

/// **A step of the pass** over a block that fits: if its header is marked,
/// the header is made black and the bit cleared.
let mat_step (w r: heap) (b: Seq.seq U32.t) (s cur e: nat) (a: hp_addr)
  : Lemma (requires mat_inv w r b s cur e /\ U64.v a == cur /\ cur < e /\ cur + words_at r cur * 8 <= e)
          (ensures (let nx = cur + words_at r cur * 8 in
                    if marked b cur
                    then mat_inv w (write_word r a (colorHeader (read_word r a) Black)) (clear_bit b cur) s nx e
                    else mat_inv w r b s nx e))
  = let wa = words_at r cur in
    let nx = cur + wa * 8 in
    on_walk_step r cur e cur;
    if marked b cur then begin
      let r' = write_word r a (colorHeader (read_word r a) Black) in
      let b' = clear_bit b cur in
      let eqs (x: hp_addr) : Lemma (x <> a ==> marked b (U64.v x) == marked b' (U64.v x))
        = clear_bit_marked b cur (U64.v x)
      in
      FStar.Classical.forall_intro eqs;
      clear_bit_marked b cur cur;
      wm_blacken r (marked b) (marked b') a;
      blacken_agree r a;
      let before (x: nat) : Lemma (s <= x /\ x < nx ==> not (marked b' x))
        = clear_bit_marked b cur x;
          if cur < x && x < nx then one_block r b cur e x
      in
      FStar.Classical.forall_intro before;
      let after (x: nat) : Lemma (nx <= x /\ x < e /\ marked b' x ==> on_walk r' nx e x)
        = clear_bit_marked b cur x;
          if nx <= x && x < e && marked b' x then begin
            on_walk_step r cur e x;
            on_walk_local r' r (cur + 8) nx e x
          end
      in
      FStar.Classical.forall_intro after
    end else begin
      let before (x: nat) : Lemma (s <= x /\ x < nx ==> not (marked b x))
        = if cur < x && x < nx then one_block r b cur e x
      in
      FStar.Classical.forall_intro before;
      let after (x: nat) : Lemma (nx <= x /\ x < e /\ marked b x ==> on_walk r nx e x)
        = if nx <= x && x < e && marked b x then on_walk_step r cur e x
      in
      FStar.Classical.forall_intro after
    end

/// **The end of the pass**: no mark is left in the run, which holds exactly
/// what the specification's heap holds there.
let mat_done (w r: heap) (b: Seq.seq U32.t) (s cur e: nat)
  : Lemma (requires mat_inv w r b s cur e /\ (cur >= e \/ cur + words_at r cur * 8 > e))
          (ensures (forall (x: nat). s <= x /\ x < e ==> not (marked b x)) /\ SO.hagree r w s e)
  = let none (x: nat) : Lemma (s <= x /\ x < e ==> not (marked b x))
      = if cur <= x && x < e && marked b x then on_walk_step r cur e x
    in
    FStar.Classical.forall_intro none;
    let agree (y: hp_addr) : Lemma (s <= U64.v y /\ U64.v y < e ==> read_word r y == read_word w y)
      = wm_read r (marked b) y
    in
    FStar.Classical.forall_intro agree

/// **The run sweep on the run made black**: once the run holds exactly the
/// specification's words and has no mark left, sweeping it with header
/// colours is the specification's sweep of it.
let run_sim (r w: heap) (b: Seq.seq U32.t) (pm: page_map) (h: nat{h < n_pages}) (n: pos) (fp: U64.t)
  : Lemma (requires (entry pm h).kind == LargeHead n /\ with_marks r b == w /\
                    SO.hagree r w (page_base h) (page_base (h + n)) /\
                    (forall (x: nat). page_base h <= x /\ x < page_base (h + n) ==> not (marked b x)))
          (ensures (let t = SO.sweep_unit r pm h fp in
                    let tw = SO.sweep_unit w pm h fp in
                    with_marks (SO.hp t) b == SO.hp tw /\ SO.mp t == SO.mp tw /\ SO.rp t == SO.rp tw))
  = let t = SO.sweep_unit r pm h fp in
    let tw = SO.sweep_unit w pm h fp in
    SO.unit_local r w pm pm h fp;
    SO.unit_frame r pm h fp;
    SO.unit_frame w pm h fp;
    let words (a: nat)
      : Lemma (a < heap_size /\ a % 8 == 0 ==>
               read_word (with_marks (SO.hp t) b) (U64.uint_to_t a) == read_word (SO.hp tw) (U64.uint_to_t a))
      = if a < heap_size && a % 8 = 0 then begin
          let y : hp_addr = U64.uint_to_t a in
          wm_read (SO.hp t) (marked b) y;
          wm_read r (marked b) y
        end
    in
    FStar.Classical.forall_intro words;
    HE.heap_read_word_ext (with_marks (SO.hp t) b) (SO.hp tw);
    let ent (j: nat{j < n_pages}) : Lemma (entry (SO.mp t) j == entry (SO.mp tw) j) = () in
    FStar.Classical.forall_intro ent;
    SO.map_eq (SO.mp t) (SO.mp tw)
