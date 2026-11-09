/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Survive - what the whole sweep keeps and what it frees
/// ---------------------------------------------------------------------------
///
/// From the state the mark leaves (`sweep_ready`, `mark_done`), `sweep_all`
/// gives a heap `g` in which, against the marked heap `g0`:
///   - every black object survives, white, with its size, tag and fields
///     (`black_survives`), and every object that is not free is one of
///     those (`GC.Spec.Pages.SweepAll.obj_survivor`);
///   - every word of a block that was not black lies in a free block of `g`
///     (`dead_covered`), and no word of a black one does (`live_uncovered`);
///   - a survivor has the same pointer fields, resolved the same way
///     (`pointer_fields_kept`), so the same successors in the heap graph.
///
/// `in_extent` and `blue_covered` are `GC.Spec.Coalesce.Correct`'s, word for
/// word, so that this module does not depend on the coalescing sweep.

module GC.Spec.Pages.Survive

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Walk
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Theorems
open GC.Spec.Pages.SweepAll

module U64 = FStar.UInt64
module Seq = FStar.Seq
module R = GC.Spec.Pages.Replace
module F = GC.Spec.Pages.Fill
module SU = GC.Spec.Pages.SweepUnits
module SW = GC.Spec.Pages.SweepWf
module S3 = GC.Spec.Pages.SweepStarts
module SS = GC.Spec.Pages.SweepStep
module MP = GC.Spec.Pages.MarkPhase
module HeapGraph = GC.Spec.HeapGraph

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Words and blocks (as GC.Spec.Coalesce.Correct)
/// ---------------------------------------------------------------------------

/// The walk position immediately above x.
let next_pos (g: heap) (x: obj_addr) : GTot nat =
  U64.v (hd_address x) + whsize g x * U64.v mword

/// p lies within x's header-and-fields extent.
let in_extent (g: heap) (x: obj_addr) (p: nat) : prop =
  U64.v (hd_address x) <= p /\ p < next_pos g x

/// p is covered by some blue object.
let blue_covered (g: heap) (p: nat) : prop =
  exists (x: obj_addr).
    Seq.mem x (objects zero_addr g) /\ is_blue x g /\ in_extent g x p

/// ---------------------------------------------------------------------------
/// The setting
/// ---------------------------------------------------------------------------

/// `g, st` is the whole sweep of `g0, st0`, with its invariant at the end.
let swept (g0: heap) (st0: pstate) (g: heap) (st: pstate) : prop =
  sweep_ready g0 st0 /\ mark_done g0 /\ S3.inv3 g0 st0 g st n_pages

let swept_of (g0: heap) (st0: pstate)
  : Lemma (requires sweep_ready g0 st0 /\ mark_done g0)
          (ensures (let (g, st) = sweep_all g0 st0 in
                    swept g0 st0 g st /\ pages_ok g st /\ well_formed_heap g /\ MP.all_swept st))
  = S3.sweep_all_inv3 g0 st0;
    SW.sweep_all_wf g0 st0

let swept_inv (g0: heap) (st0: pstate) (g: heap) (st: pstate)
  : Lemma (requires swept g0 st0 g st)
          (ensures inv g0 st0 g st n_pages /\ shape_ok g st.pm /\ shape_ok g0 st0.pm /\ map_ok st0.pm /\
                   (forall (i: nat{i < n_pages}). walk_page st0.pm i ==> walk_page st.pm i) /\
                   (forall (i: nat{i < n_pages}). walk_page st0.pm i ==>
                      SU.unit_ok g0 g i (span st0.pm i) /\ S3.starts_ok g0 g i (span st0.pm i)) /\
                   (forall (x: hp_addr). U64.v x >= pages_end ==> read_word g x == read_word g0 x))
  = inv_elim g0 st0 g st n_pages;
    end_facts g0 g st0 st

/// ---------------------------------------------------------------------------
/// Survivors
/// ---------------------------------------------------------------------------

/// **A black object survives**, white, with its size, tag and fields.
let black_survives (g0: heap) (st0: pstate) (g: heap) (st: pstate) (x: obj_addr)
  : Lemma (requires swept g0 st0 g st /\ Seq.mem x (objects zero_addr g0) /\ is_black x g0)
          (ensures Seq.mem x (objects zero_addr g) /\ is_white x g /\ ~(is_blue x g) /\
                   read_word g (hd_address x) == colorHeader (read_word g0 (hd_address x)) White /\
                   wosize_of_object x g == wosize_of_object x g0 /\
                   tag_of_object x g == tag_of_object x g0 /\
                   (forall (b: hp_addr). U64.v x <= U64.v b /\
                      U64.v b < U64.v x + U64.v (wosize_of_object x g0) * 8 ==>
                      read_word g b == read_word g0 b))
  = let h = U64.v x - 8 in
    swept_inv g0 st0 g st;
    hd_address_spec x;
    R.obj_iff g0 x;
    R.hdr_obj g0 x;
    is_black_iff x g0;
    black_kept g0 g st0 st h;
    colorHeader_preserves_wosize (hdr g0 h) White;
    colorHeader_getColor (hdr g0 h) White;
    R.hdr_obj g x;
    R.obj_iff g x;
    is_white_iff x g;
    is_blue_iff x g;
    whiten_tag x g0;
    tag_of_object_spec x g;
    tag_of_object_spec x g0;
    wosize_of_object_spec x g;
    wosize_of_object_spec x g0

/// An object of the swept heap that is not free is a black object of the
/// marked heap (`SweepAll.obj_survivor`), white.
let survivor (g0: heap) (st0: pstate) (g: heap) (st: pstate) (x: obj_addr)
  : Lemma (requires swept g0 st0 g st /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))
          (ensures Seq.mem x (objects zero_addr g0) /\ is_black x g0 /\ is_white x g)
  = swept_inv g0 st0 g st;
    obj_survivor g0 g st0 st x;
    black_survives g0 st0 g st x

/// ---------------------------------------------------------------------------
/// Covering a word
/// ---------------------------------------------------------------------------

/// The block of a walk that covers `p`.
#push-options "--fuel 1 --ifuel 1"
let rec cover_at (g: heap) (s e p: nat)
  : Ghost nat (requires steps_to g s e /\ s <= p /\ p < e)
              (ensures fun b -> steps_to g s b /\ b <= p /\ b % 8 == 0 /\ b < heap_size /\
                             p < b + words_at g b * 8 /\ b + words_at g b * 8 <= e)
              (decreases (e - s))
  = steps_to_le g s e;
    let sa = mk_hp_addr s in
    steps_to_next g sa e;
    R.block_bytes_words g s;
    let nx = s + words_at g s * 8 in
    if p < nx then (steps_to_refl g s; s)
    else begin
      let b = cover_at g nx e p in
      steps_to_one g sa nx;
      steps_to_trans g s nx b;
      b
    end
#pop-options

/// The end of a unit is a walk position of any heap of the right shape.
let unit_end (g: heap) (pm: page_map) (i: nat{i < n_pages})
  : Lemma (requires shape_ok g pm /\ walk_page pm i)
          (ensures i + span pm i <= n_pages /\ steps_to g (page_base i) (page_base (i + span pm i)))
  = next_walk_page pm i i;
    let j = i + span pm i in
    walk_pages_reached g pm i;
    walk_pages_reached g pm j;
    page_base_mono i j;
    R.steps_to_det g (U64.v zero_addr) (page_base i) (page_base j)

/// Two walk blocks that cover the same word are the same block.
let same_cover (g: heap) (s a b p: nat)
  : Lemma (requires steps_to g s a /\ steps_to g s b /\
                    a <= p /\ p < a + words_at g a * 8 /\ b <= p /\ p < b + words_at g b * 8)
          (ensures a == b)
  = if a < b then R.block_before g s a b
    else if b < a then R.block_before g s b a

/// The tail of the heap, past the pages.
let tail_block (g0: heap) (st0: pstate) (g: heap) (st: pstate) (x: obj_addr)
  : Lemma (requires swept g0 st0 g st /\ Seq.mem x (objects zero_addr g0) /\ U64.v x - 8 >= pages_end)
          (ensures U64.v x - 8 == pages_end /\ Seq.mem x (objects zero_addr g) /\ is_blue x g /\
                   read_word g (hd_address x) == read_word g0 (hd_address x))
  = swept_inv g0 st0 g st;
    let h = U64.v x - 8 in
    hd_address_spec x;
    R.obj_iff g0 x;
    R.hdr_obj g0 x;
    pages_end_bound ();
    page_base_aligned n_pages;
    walk_pages_reached g0 st0.pm n_pages;
    walk_pages_reached g st.pm n_pages;
    R.steps_to_det g0 (U64.v zero_addr) pages_end h;
    assert (heap_size - pages_end >= 16);
    assert (blue_block g0 pages_end ((heap_size - pages_end) / 8));
    if h > pages_end then begin
      steps_to_refl g0 pages_end;
      R.block_before g0 pages_end pages_end h
    end;
    assert (read_word g (hd_address x) == read_word g0 (hd_address x));
    R.hdr_obj g x;
    R.obj_iff g x;
    is_blue_iff x g

/// A free block that covers a word of a block of the marked heap is not
/// the last word of the heap: no page starts there, and no block of the
/// marked heap starts inside another.
let not_last (g0 g: heap) (i k: nat) (h b p: nat)
  : Lemma (requires S3.starts_ok g0 g i k /\ i + k <= n_pages /\
                    steps_to g (page_base i) b /\ b < page_base (i + k) /\ color_at g b == Blue /\
                    b % 8 == 0 /\ b <= p /\ p < heap_size /\
                    steps_to g0 (page_base i) h /\ h + 8 < heap_size /\ h <= p /\ p < h + words_at g0 h * 8)
          (ensures b + 8 < heap_size)
  = assert_norm (U64.v mword == 8);
    SS.aligned_lt b heap_size;
    page_base_mono (i + k) n_pages;
    if b + 8 = heap_size then begin
      if FStar.IndefiniteDescription.strong_excluded_middle (S3.is_page_start b) then
        eliminate exists (j: nat). b == page_base j
        with begin
          if j < n_pages then begin
            page_base_mono (j + 1) n_pages;
            FStar.Math.Lemmas.distributivity_add_left j 1 page_bytes;
            cls_bounds 0
          end
          else FStar.Math.Lemmas.lemma_mult_le_right page_bytes n_pages j
        end
      else R.block_before g0 (page_base i) h b
    end

/// The free block of a unit that covers a dead word.
let dead_in_unit (g0 g: heap) (i k: nat) (h p: nat)
  : Ghost nat
    (requires SU.unit_ok g0 g i k /\ S3.starts_ok g0 g i k /\ i + k <= n_pages /\
              steps_to g0 (page_base i) h /\ h + 8 < heap_size /\ color_at g0 h =!= Black /\
              page_base i <= p /\ h <= p /\ p < h + words_at g0 h * 8 /\ h + words_at g0 h * 8 <= page_base (i + k))
    (ensures fun b -> steps_to g (page_base i) b /\ color_at g b == Blue /\ b % 8 == 0 /\
                     b <= p /\ p < b + words_at g b * 8 /\ b + 8 < heap_size /\
                     b + words_at g b * 8 <= heap_size)
  = page_base_mono (i + k) n_pages;
    let b = cover_at g (page_base i) (page_base (i + k)) p in
    if color_at g b <> Blue then begin
      colorHeader_preserves_wosize (hdr g0 b) White;
      same_cover g0 (page_base i) h b p
    end;
    not_last g0 g i k h b p;
    b

/// The object whose header is at `b`.
let obj_at (b: nat{b % 8 == 0 /\ b + 8 < heap_size}) : obj_addr =
  assert_norm (U64.v mword == 8);
  FStar.Math.Lemmas.lemma_mod_plus b 1 8;
  U64.uint_to_t (b + 8)

/// A free block of the walk that covers `p` and fits makes `p` covered.
let blue_obj (g: heap) (b p: nat)
  : Lemma (requires steps_to g (U64.v zero_addr) b /\ color_at g b == Blue /\ b % 8 == 0 /\
                    b <= p /\ p < b + words_at g b * 8 /\ b + 8 < heap_size /\
                    b + words_at g b * 8 <= heap_size)
          (ensures blue_covered g p)
  = let y = obj_at b in
    hd_address_spec y;
    R.obj_iff g y;
    R.hdr_obj g y;
    is_blue_iff y g;
    assert (in_extent g y p)

/// **Every word of a block that was not black is free after the sweep.**
let dead_covered (g0: heap) (st0: pstate) (g: heap) (st: pstate) (x: obj_addr) (p: nat)
  : Lemma (requires swept g0 st0 g st /\ Seq.mem x (objects zero_addr g0) /\ ~(is_black x g0) /\
                    in_extent g0 x p)
          (ensures blue_covered g p)
  = swept_inv g0 st0 g st;
    let h = U64.v x - 8 in
    hd_address_spec x;
    R.obj_iff g0 x;
    R.hdr_obj g0 x;
    is_black_iff x g0;
    assert (next_pos g0 x == h + words_at g0 h * 8);
    if h >= pages_end then begin
      tail_block g0 st0 g st x;
      R.hdr_obj g x;
      wosize_of_object_spec x g;
      wosize_of_object_spec x g0;
      assert (in_extent g x p)
    end else begin
      SW.in_unit_lt g0 st0.pm st0.pm h;
      eliminate exists (i: nat{i < n_pages}).
        walk_page st0.pm i /\ page_base i <= h /\ h < page_base (i + span st0.pm i) /\
        steps_to g0 (page_base i) h
      with begin
        let k = span st0.pm i in
        let e = page_base (i + k) in
        unit_end g0 st0.pm i;
        R.steps_to_det g0 (page_base i) h e;
        steps_to_next g0 (mk_hp_addr h) e;
        R.block_bytes_words g0 h;
        let b = dead_in_unit g0 g i k h p in
        walk_pages_reached g st.pm i;
        steps_to_trans g (U64.v zero_addr) (page_base i) b;
        blue_obj g b p
      end
    end

/// **No word of a black object is free after the sweep.**
let live_uncovered (g0: heap) (st0: pstate) (g: heap) (st: pstate) (x: obj_addr) (p: nat)
  : Lemma (requires swept g0 st0 g st /\ Seq.mem x (objects zero_addr g0) /\ is_black x g0 /\
                    in_extent g0 x p)
          (ensures ~(blue_covered g p))
  = black_survives g0 st0 g st x;
    let aux (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g) /\ is_blue y g /\ in_extent g y p)
              (ensures False)
      = hd_address_spec x;
        hd_address_spec y;
        R.obj_iff g y;
        F.apart g x (U64.v y - 8);
        R.hdr_obj g y;
        wosize_of_object_spec y g
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// ---------------------------------------------------------------------------
/// The heap graph
/// ---------------------------------------------------------------------------

/// A pointer field of a survivor resolves the same in both heaps.
let field_kept (g0: heap) (st0: pstate) (g: heap) (st: pstate) (x: obj_addr) (i: U64.t{U64.v i >= 1})
  : Lemma (requires swept g0 st0 g st /\ Seq.mem x (objects zero_addr g0) /\ is_black x g0 /\
                    ~(is_no_scan x g0) /\ U64.v i <= U64.v (wosize_of_object x g0))
          (ensures HeapGraph.get_field g0 x i == HeapGraph.get_field g x i /\
                   HeapGraph.resolve_field g0 (HeapGraph.get_field g0 x i) ==
                   HeapGraph.resolve_field g (HeapGraph.get_field g0 x i))
  = swept_inv g0 st0 g st;
    black_survives g0 st0 g st x;
    let wz = wosize_of_object x g0 in
    wosize_of_object_bound x g0;
    hd_address_spec x;
    R.obj_iff g0 x;
    R.hdr_obj g0 x;
    HeapGraph.get_field_addr_eq g0 x i;
    HeapGraph.get_field_addr_eq g x i;
    let j = U64.v i - 1 in
    let fa = R.field_addr x j in
    assert (HeapGraph.get_field g0 x i == read_word g0 fa);
    assert (HeapGraph.get_field g x i == read_word g fa);
    let v = read_word g0 fa in
    if is_pointer v then begin
      let t : obj_addr = v in
      target_black g0 x j t;
      target_after g0 g st0 st t
    end

#push-options "--fuel 1 --ifuel 1"
let rec aux_kept (g0: heap) (st0: pstate) (g: heap) (st: pstate) (x: obj_addr)
                 (i: U64.t{U64.v i >= 1}) (ws: U64.t)
  : Lemma (requires swept g0 st0 g st /\ Seq.mem x (objects zero_addr g0) /\ is_black x g0 /\
                    ~(is_no_scan x g0) /\ U64.v ws <= U64.v (wosize_of_object x g0))
          (ensures HeapGraph.get_pointer_fields_aux g0 x i ws ==
                   HeapGraph.get_pointer_fields_aux g x i ws)
          (decreases (U64.v ws - U64.v i + 1))
  = if U64.v i > U64.v ws then ()
    else begin
      field_kept g0 st0 g st x i;
      if U64.v i < U64.v ws then aux_kept g0 st0 g st x (U64.add i 1UL) ws
    end
#pop-options

/// **A survivor has the same pointer fields.**
let pointer_fields_kept (g0: heap) (st0: pstate) (g: heap) (st: pstate) (x: obj_addr)
  : Lemma (requires swept g0 st0 g st /\ Seq.mem x (objects zero_addr g0) /\ is_black x g0)
          (ensures HeapGraph.get_pointer_fields g0 x == HeapGraph.get_pointer_fields g x)
  = black_survives g0 st0 g st x;
    is_no_scan_spec x g0;
    is_no_scan_spec x g;
    is_blue_iff x g0;
    is_black_iff x g0;
    if not (is_no_scan x g0) then aux_kept g0 st0 g st x 1UL (wosize_of_object x g0)
