/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Step - the parts every allocator step shares
/// ---------------------------------------------------------------------------
///
///   - `pages_ok` taken apart into page-local clauses and global ones;
///   - two steps of `cleared_ok` compose (taking a free page, then a slot);
///   - a rewrite of pages that hold no run keeps every other page
///     (`others_local`) and the large lists (`lview_away`).

module GC.Spec.Pages.Step

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
open GC.Spec.Pages.Frame
open GC.Spec.Pages.Replace
open GC.Spec.Pages.Cells
open GC.Spec.Pages.Theorems

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module Mark = GC.Spec.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// pages_ok, taken apart
/// ---------------------------------------------------------------------------

let pages_ok_elim (g: heap) (st: pstate)
  : Lemma (requires pages_ok g st)
          (ensures map_ok st.pm /\ (forall (i: nat{i < n_pages}). page_local g st.pm i) /\
                   tail_shape g /\ avail_ok st /\ large_ok g st /\ Mark.no_pointer_to_blue g /\
                   shape_ok g st.pm)
  = reveal_opaque (`%pages_ok) pages_ok

let pages_ok_intro (g: heap) (st: pstate)
  : Lemma (requires map_ok st.pm /\ (forall (i: nat{i < n_pages}). page_local g st.pm i) /\
                    tail_shape g /\ avail_ok st /\ large_ok g st /\ Mark.no_pointer_to_blue g)
          (ensures pages_ok g st)
  = reveal_opaque (`%pages_ok) pages_ok

/// ---------------------------------------------------------------------------
/// Composing steps
/// ---------------------------------------------------------------------------

let step_ok (g g1: heap) (st st1: pstate) : prop =
  others_unchanged g g1 /\ unswept_unchanged g g1 st st1

/// What the allocator proves of the heap it makes when it clears the new
/// object's fields: `alloc_ok`'s statement before stage 2's change to
/// uninitialised fields, with `pages_ok` and `well_formed_heap` of the heap
/// itself.  `GC.Spec.Pages.Alloc` derives `alloc_ok` from it.
let cleared_ok (g g': heap) (st st': pstate) (wz: nat) (obj: U64.t) : prop =
  (obj == 0UL ==> g' == g /\ st' == st /\ (wz + 1 < pow2 54 ==> no_fit g st (wz + 1))) /\
  (obj =!= 0UL ==>
     U64.v obj >= 8 /\ U64.v obj < heap_size /\ U64.v obj % 8 == 0 /\
     (let x : obj_addr = obj in
      Seq.mem x (objects zero_addr g') /\
      U64.v (wosize_of_object x g') == wz /\
      is_white x g' /\
      ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))) /\
     pages_ok g' st' /\
     well_formed_heap g' /\
     others_unchanged g g' /\
     unswept_unchanged g g' st st')

let others_trans (g g1 g2: heap)
  : Lemma (requires others_unchanged g g1 /\ others_unchanged g1 g2)
          (ensures others_unchanged g g2)
  = let aux (x: obj_addr)
      : Lemma (requires Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))
              (ensures Seq.mem x (objects zero_addr g2) /\
                       read_word g2 (hd_address x) == read_word g (hd_address x) /\
                       (forall (b: hp_addr). U64.v x <= U64.v b /\
                          U64.v b < U64.v x + U64.v (wosize_of_object x g) * 8 ==>
                          read_word g2 b == read_word g b))
      = color_of_header_eq x g g1;
        wosize_of_object_spec x g;
        wosize_of_object_spec x g1
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

let cleared_ok_compose (g g1 g': heap) (st st1 st': pstate) (wz: nat) (obj: U64.t)
  : Lemma (requires step_ok g g1 st st1 /\ cleared_ok g1 g' st1 st' wz obj /\ obj =!= 0UL)
          (ensures cleared_ok g g' st st' wz obj)
  = others_trans g g1 g';
    let x : obj_addr = obj in
    if Seq.mem x (objects zero_addr g) && not (is_blue x g) then color_of_header_eq x g g1

/// ---------------------------------------------------------------------------
/// The page map
/// ---------------------------------------------------------------------------

/// `map_ok` reads only kinds and swept bits.
let map_ok_same_kinds (pm pm': page_map)
  : Lemma (requires map_ok pm /\
                    (forall (i: nat{i < n_pages}).
                       (entry pm' i).kind == (entry pm i).kind /\ (entry pm' i).swept == (entry pm i).swept))
          (ensures map_ok pm')
  = let aux (i: nat{i < n_pages}) : Lemma (run_ok pm' i /\ cont_ok pm' i /\ free_ok pm' i)
      = assert (run_ok pm i /\ cont_ok pm i /\ free_ok pm i)
    in
    FStar.Classical.forall_intro aux

/// `in_swept_run` reads only the run heads.
let swept_run_same (pm pm': page_map)
  : Lemma (requires forall (h: nat{h < n_pages}).
                      (LargeHead? (entry pm' h).kind <==> LargeHead? (entry pm h).kind) /\
                      (LargeHead? (entry pm h).kind ==> entry pm' h == entry pm h))
          (ensures forall (a: nat). in_swept_run pm' a <==> in_swept_run pm a)
  = ()

/// A span that does not start in pages `p0 .. p1 - 1`, the first of which
/// does not continue a run, lies wholly before or after them.
let span_apart (pm: page_map) (p0 p1: nat) (j: nat{j < n_pages})
  : Lemma (requires map_ok pm /\ p0 < p1 /\ p1 <= n_pages /\ (j < p0 \/ j >= p1) /\
                    (entry pm p0).kind =!= LargeCont)
          (ensures page_base (span_end pm j) <= page_base p0 \/ page_base j >= page_base p1)
  = assert (run_ok pm j);
    if j < p0 then begin
      if span_end pm j > p0 then assert ((entry pm p0).kind == LargeCont);
      page_base_mono (span_end pm j) p0
    end
    else page_base_mono p1 j

/// **A rewrite of pages `p0 .. p1 - 1` keeps every other page**, when page
/// `p0` starts a span (so the rewritten pages are whole spans).
let others_local (g g': heap) (pm pm': page_map) (p0 p1: nat)
  : Lemma (requires map_ok pm /\ p0 < p1 /\ p1 <= n_pages /\
                    (forall (i: nat{i < n_pages}). page_local g pm i) /\
                    (forall (x: hp_addr). U64.v x < page_base p0 \/ U64.v x >= page_base p1 ==>
                       read_word g' x == read_word g x) /\
                    (entry pm p0).kind =!= LargeCont /\
                    (forall (j: nat{j < n_pages}). j < p0 \/ j >= p1 ==> entry pm' j == entry pm j))
          (ensures forall (j: nat{j < n_pages}). j < p0 \/ j >= p1 ==> page_local g' pm' j)
  = let aux (j: nat{j < n_pages})
      : Lemma (j < p0 \/ j >= p1 ==> page_local g' pm' j)
      = if j < p0 || j >= p1 then begin
          span_apart pm p0 p1 j;
          page_local_frame g g' pm pm' j
        end
    in
    FStar.Classical.forall_intro aux

/// The heap's tail is past every page.
let tail_kept (g g': heap) (p1: nat)
  : Lemma (requires p1 <= n_pages /\
                    (forall (x: hp_addr). U64.v x >= page_base p1 ==> read_word g' x == read_word g x) /\
                    tail_shape g)
          (ensures tail_shape g')
  = page_base_mono p1 n_pages;
    tail_frame g g'

/// ---------------------------------------------------------------------------
/// The large lists, away from runs
/// ---------------------------------------------------------------------------

let cell_away (g g': heap) (a e: nat) (pm: page_map) (y: obj_addr)
  : Lemma (requires replaces g g' a e /\ in_swept_run pm (U64.v (hd_address y)) /\
                    (forall (x: nat). a <= x /\ x < e ==> ~(in_swept_run pm x)))
          (ensures (Seq.mem y (objects zero_addr g) <==> Seq.mem y (objects zero_addr g')) /\
                   (Seq.mem y (objects zero_addr g) ==>
                      read_word g' (hd_address y) == read_word g (hd_address y) /\
                      (U64.v (wosize_of_object y g) >= 1 ==>
                         read_word g' (y <: hp_addr) == read_word g (y <: hp_addr))))
  = hd_address_spec y;
    replace_obj_out g g' a e y;
    hdr_obj g y

/// **A rewrite outside every swept run keeps the large lists.**
let lview_away (g g': heap) (a e: nat) (st st': pstate) (cs: list obj_addr)
  : Lemma (requires replaces g g' a e /\ lview g st cs /\ st'.large == st.large /\
                    (forall (x: nat). in_swept_run st'.pm x <==> in_swept_run st.pm x) /\
                    (forall (x: nat). a <= x /\ x < e ==> ~(in_swept_run st.pm x)))
          (ensures lview g' st' cs)
  = let in_cs (y: obj_addr)
      : Lemma (requires L.mem y cs)
              (ensures Seq.mem y (objects zero_addr g') /\
                       U64.v (wosize_of_object y g') >= 1 /\
                       read_word g' (y <: hp_addr) == read_word g (y <: hp_addr) /\
                       is_blue y g' /\ large_listable g' st'.pm y)
      = cells_mem g (large_head st) cs y;
        cell_away g g' a e st.pm y;
        color_of_header_eq y g g';
        wosize_of_object_spec y g;
        wosize_of_object_spec y g'
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires in_cs);
    cells_frame g g' (large_head st) cs;
    let complete (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g') /\ is_blue y g' /\ large_listable g' st'.pm y)
              (ensures L.mem y cs)
      = cell_away g g' a e st.pm y;
        color_of_header_eq y g g';
        wosize_of_object_spec y g;
        wosize_of_object_spec y g'
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires complete)
