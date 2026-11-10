/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.SweepWf - the swept heap is well formed
/// ---------------------------------------------------------------------------
///
/// **`sweep_all_wf`**: from the state the mark leaves (`sweep_ready`,
/// `mark_done`), `sweep_all` gives a heap that satisfies `well_formed_heap`,
/// as well as `pages_ok` (`GC.Spec.Pages.SweepAll.sweep_all_correct`).
///
///   - Part 1 holds of every heap.
///   - Parts 2 and 3: a pointer field of a survivor is the field of a black
///     object of the marked heap, so its target was black, survived, and
///     resolves to the same object (`field_target`), as for L10
///     (`SweepAll.target_after`).
///   - Part 4, no object is infix: a survivor keeps its tag; a free block
///     has a new header of tag 0 or is a block of the marked heap, kept
///     (`GC.Spec.Pages.SweepTags.blue_ok`, carried through the sweep by
///     `inv2`).

module GC.Spec.Pages.SweepWf

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
open GC.Spec.Pages.SweepTags

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module R = GC.Spec.Pages.Replace
module FR = GC.Spec.Pages.Frame
module SP = GC.Spec.Pages.SweepPage
module SR = GC.Spec.Pages.SweepRun
module SS = GC.Spec.Pages.SweepStep
module SU = GC.Spec.Pages.SweepUnits
module Mark = GC.Spec.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The tag facts through the sweep
/// ---------------------------------------------------------------------------

let tags_before (g0: heap) (st0: pstate) (g: heap) (p: nat) : prop =
  forall (i: nat{i < n_pages}). i < p /\ walk_page st0.pm i ==> blue_ok g0 g i (span st0.pm i)

let inv2 (g0: heap) (st0: pstate) (g: heap) (st: pstate) (p: nat) : prop =
  inv g0 st0 g st p /\ tags_before g0 st0 g p

/// What the step at `p` writes: only the unit at `p`.
let step_frame (g0 g: heap) (st0 st: pstate) (p: nat{p < n_pages})
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st p)
          (ensures (let (g', _) = step g st p in
                    forall (x: hp_addr). U64.v x < page_base p ==> read_word g' x == read_word g x))
  = inv_elim g0 st0 g st p;
    assert (entry st.pm p == entry st0.pm p);
    page_base_aligned p;
    match (entry st0.pm p).kind with
    | Free -> ()
    | Pool c ->
      marked_pool_at g0 g st0 st p c;
      SP.sweep_page_correct ();
      let (g', e) = SP.sweep_page g st.pm p in
      assert (sweep_page_ok g st.pm p c g' e);
      assert (fst (step g st p) == g');
      let below (x: hp_addr) : Lemma (U64.v x < page_base p ==> read_word g' x == read_word g x)
        = if U64.v x < page_base p then SS.aligned_lt (U64.v x) (page_base p)
      in
      FStar.Classical.forall_intro below
    | LargeHead _ ->
      marked_run_at g0 g st0 st p;
      SR.sweep_run_correct ();
      let (g', pm', fp') = SR.sweep_run g st.pm p (GC.Spec.Pages.Cells.large_head st) in
      assert (sweep_run_ok g st.pm p (GC.Spec.Pages.Cells.large_head st) g' pm' fp');
      assert (fst (step g st p) == g')
    | LargeCont -> ()

/// The new unit's tag facts, against the marked heap.
let step_tags (g0 g: heap) (st0 st: pstate) (p: nat{p < n_pages})
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st p)
          (ensures (let (g', _) = step g st p in blue_ok g0 g' p (span st0.pm p)))
  = inv_elim g0 st0 g st p;
    let (g', st') = step g st p in
    let k = span st0.pm p in
    assert (FR.kept_range g g0 (page_base p) (page_base (p + k)));
    page_base_mono p (p + k);
    match (entry st0.pm p).kind with
    | Free ->
      kept_blue_ok g0 g p k
    | Pool c ->
      marked_pool_at g0 g st0 st p c;
      pool_blue_ok g st.pm p c;
      blue_ok_frame g g' g0 g' p k
    | LargeHead _ ->
      marked_run_at g0 g st0 st p;
      run_blue_ok g st.pm p (GC.Spec.Pages.Cells.large_head st);
      blue_ok_frame g g' g0 g' p k

let inv2_step (g0 g: heap) (st0 st: pstate) (p: nat{p < n_pages})
  : Lemma (requires sweep_ready g0 st0 /\ inv2 g0 st0 g st p)
          (ensures (let (g', st') = step g st p in inv2 g0 st0 g' st' (p + span st.pm p)))
  = inv_elim g0 st0 g st p;
    inv_step g0 g st0 st p;
    step_frame g0 g st0 st p;
    let (g', st') = step g st p in
    let k = span st0.pm p in
    assert (map_ok st0.pm);
    next_walk_page st0.pm p p;
    let old (i: nat{i < n_pages})
      : Lemma (i < p + k /\ walk_page st0.pm i ==> blue_ok g0 g' i (span st0.pm i))
      = if i < p + k && walk_page st0.pm i then begin
          if i < p then begin
            assert (i + span st0.pm i <= p);
            page_base_mono (i + span st0.pm i) p;
            blue_ok_frame g0 g g0 g' i (span st0.pm i)
          end
          else if i = p then step_tags g0 g st0 st p
          else next_walk_page st0.pm p i
        end
    in
    FStar.Classical.forall_intro old

#push-options "--fuel 1"
let rec sweep_from_inv2 (g0 g: heap) (st0 st: pstate) (p: nat)
  : Lemma (requires sweep_ready g0 st0 /\ inv2 g0 st0 g st p)
          (ensures (let (g', st') = sweep_from g st p in inv2 g0 st0 g' st' n_pages))
          (decreases (if p < n_pages then n_pages - p else 0))
  = inv_bound g0 st0 g st p;
    if p >= n_pages then ()
    else begin
      inv2_step g0 g st0 st p;
      let (g', st') = step g st p in
      sweep_from_inv2 g0 g' st0 st' (p + span st.pm p)
    end
#pop-options

let inv2_init (g: heap) (st: pstate)
  : Lemma (requires sweep_ready g st) (ensures inv2 g st g st 0)
  = inv_init g st

let sweep_all_inv2 (g: heap) (st: pstate)
  : Lemma (requires sweep_ready g st)
          (ensures (let (g', st') = sweep_all g st in inv2 g st g' st' n_pages))
  = inv_init g st;
    sweep_from_inv2 g g st st 0

/// ---------------------------------------------------------------------------
/// Part 4: no object is infix
/// ---------------------------------------------------------------------------

/// The unit a position of the pages lies in (as `SweepAll.in_unit`, for
/// any block).
let in_unit_lt (g: heap) (pm0 pm: page_map) (h: nat)
  : Lemma (requires shape_ok g pm /\ map_ok pm0 /\
                    (forall (i: nat{i < n_pages}). walk_page pm0 i ==> walk_page pm i) /\
                    steps_to g (U64.v zero_addr) h /\ h < pages_end)
          (ensures exists (i: nat{i < n_pages}).
                     walk_page pm0 i /\ page_base i <= h /\ h < page_base (i + span pm0 i) /\
                     steps_to g (page_base i) h)
  = steps_to_le g (U64.v zero_addr) h;
    page_of_spec h;
    let j = page_of h in
    let found (i: nat{i < n_pages})
      : Lemma (requires walk_page pm0 i /\ page_base i <= h /\ h < page_base (i + span pm0 i))
              (ensures steps_to g (page_base i) h)
      = walk_pages_reached g pm i;
        R.steps_to_det g (U64.v zero_addr) (page_base i) h
    in
    if walk_page pm0 j then begin
      assert (span pm0 j >= 1);
      page_base_mono (j + 1) (j + span pm0 j);
      found j
    end
    else begin
      assert (cont_ok pm0 j);
      eliminate exists (u: nat{u < n_pages}). u < j /\ in_run pm0 u j
      with begin
        page_base_mono u j;
        page_base_mono (j + 1) (u + run_len (entry pm0 u).kind);
        found u
      end
    end

/// A block of the marked heap with the same header as `x` in the swept heap
/// makes `x` an object of the marked heap with the same tag.
let same_block (g0 g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr g) /\ steps_to g0 R.z (U64.v x - 8) /\
                    hdr g (U64.v x - 8) == hdr g0 (U64.v x - 8))
          (ensures Seq.mem x (objects zero_addr g0) /\ tag_of_object x g0 == tag_of_object x g)
  = R.obj_iff g x;
    R.obj_iff g0 x;
    R.hdr_obj g x;
    R.hdr_obj g0 x

let not_infix_of (g0 g: heap) (x: obj_addr)
  : Lemma (requires well_formed_heap g0 /\ Seq.mem x (objects zero_addr g0) /\
                    tag_of_object x g0 == tag_of_object x g)
          (ensures ~(is_infix x g))
  = reveal_opaque (`%well_formed_heap) well_formed_heap;
    is_infix_spec x g;
    is_infix_spec x g0

let tag0_not_infix (g: heap) (x: obj_addr)
  : Lemma (requires getTag (hdr g (U64.v x - 8)) == 0UL) (ensures ~(is_infix x g))
  = R.hdr_obj g x;
    is_infix_spec x g;
    infix_tag_val ()

/// A free block of the swept heap is not infix.
let blue_not_infix (g0 g: heap) (st0 st: pstate) (x: obj_addr)
  : Lemma (requires sweep_ready g0 st0 /\ mark_done g0 /\ inv2 g0 st0 g st n_pages /\
                    Seq.mem x (objects zero_addr g) /\ is_blue x g)
          (ensures ~(is_infix x g))
  = let h = U64.v x - 8 in
    inv_elim g0 st0 g st n_pages;
    end_facts g0 g st0 st;
    R.obj_iff g x;
    R.hdr_obj g x;
    is_blue_iff x g;
    pages_end_bound ();
    page_base_aligned n_pages;
    if h < pages_end then begin
      in_unit_lt g st0.pm st.pm h;
      eliminate exists (i: nat{i < n_pages}).
        walk_page st0.pm i /\ page_base i <= h /\ h < page_base (i + span st0.pm i) /\
        steps_to g (page_base i) h
      with begin
        assert (blue_ok g0 g i (span st0.pm i));
        if getTag (hdr g h) = 0UL then tag0_not_infix g x
        else begin
          walk_pages_reached g0 st0.pm i;
          steps_to_trans g0 R.z (page_base i) h;
          same_block g0 g x;
          not_infix_of g0 g x
        end
      end
    end else begin
      (* the heap's tail is kept from the marked heap *)
      walk_pages_reached g st.pm n_pages;
      walk_pages_reached g0 st0.pm n_pages;
      R.steps_to_det g R.z pages_end h;
      steps_to_frame g g0 pages_end h;
      steps_to_trans g0 R.z pages_end h;
      hd_address_spec x;
      assert (U64.v (hd_address x) >= page_base n_pages);
      assert (read_word g (hd_address x) == read_word g0 (hd_address x));
      R.hdr_obj g0 x;
      same_block g0 g x;
      not_infix_of g0 g x
    end

let part4_after (g0 g: heap) (st0 st: pstate)
  : Lemma (requires sweep_ready g0 st0 /\ mark_done g0 /\ inv2 g0 st0 g st n_pages)
          (ensures well_formed_heap_part4 g)
  = let one (x: obj_addr) : Lemma (Seq.mem x (objects zero_addr g) ==> ~(is_infix x g))
      = if Seq.mem x (objects zero_addr g) then begin
          if FStar.IndefiniteDescription.strong_excluded_middle (is_blue x g)
          then blue_not_infix g0 g st0 st x
          else begin
            obj_survivor g0 g st0 st x;
            not_infix_of g0 g x
          end
        end
    in
    FStar.Classical.forall_intro one

/// ---------------------------------------------------------------------------
/// Parts 2 and 3: field targets
/// ---------------------------------------------------------------------------

/// A black target of the marked heap is an object of the swept heap,
/// resolved the same way, and its infix address stays well formed.
let target_in (g0 g: heap) (st0 st: pstate) (v: obj_addr)
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st n_pages /\
                    Seq.mem (resolve_object v g0) (objects zero_addr g0) /\
                    infix_addr_wf g0 (objects zero_addr g0) v /\
                    is_black (resolve_object v g0) g0)
          (ensures Seq.mem (resolve_object v g) (objects zero_addr g) /\
                   infix_addr_wf g (objects zero_addr g) v)
  = target_after g0 g st0 st v;
    let r = resolve_object v g0 in
    let hr = U64.v r - 8 in
    hd_address_spec r;
    R.hdr_obj g0 r;
    R.obj_iff g0 r;
    is_black_iff r g0;
    black_kept g0 g st0 st hr;
    R.hdr_obj g r;
    colorHeader_preserves_wosize (hdr g0 hr) White;
    R.obj_iff g r;
    whiten_tag r g0;
    tag_of_object_spec r g;
    tag_of_object_spec r g0;
    is_closure_spec r g;
    is_closure_spec r g0;
    wosize_of_object_spec r g;
    wosize_of_object_spec r g0;
    if is_infix v g0 then begin
      infix_inside g0 v;
      hd_address_spec v;
      assert (read_word g (hd_address v) == read_word g0 (hd_address v));
      resolve_object_locality v g0 g;
      infix_addr_wf_elim g0 (objects zero_addr g0) v;
      parent_closure_addr_nat_spec v g0;
      resolve_infix_spec v g0;
      infix_addr_wf_transfer g0 g (objects zero_addr g0) (objects zero_addr g) v
    end else begin
      resolve_non_infix v g0;
      is_infix_spec v g0;
      is_infix_spec v g;
      resolve_non_infix v g;
      infix_addr_wf_non_infix g (objects zero_addr g) v
    end

/// A pointer field of an object of the swept heap.
let field_target (g0 g: heap) (st0 st: pstate) (src: obj_addr) (j: nat)
  : Lemma (requires sweep_ready g0 st0 /\ mark_done g0 /\ inv g0 st0 g st n_pages /\
                    Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                    j < U64.v (wosize_of_object src g) /\ U64.v src + j * 8 + 8 <= heap_size)
          (ensures (let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                    is_pointer v ==>
                    Seq.mem (resolve_object (v <: obj_addr) g) (objects zero_addr g) /\
                    infix_addr_wf g (objects zero_addr g) (v <: obj_addr)))
  = let fa = R.field_addr src j in
    assert (U64.uint_to_t (U64.v src + j * 8) == fa);
    let v = read_word g fa in
    if is_pointer v then begin
      obj_survivor g0 g st0 st src;
      assert (read_word g0 fa == v);
      is_no_scan_spec src g;
      is_no_scan_spec src g0;
      target_black g0 src j (v <: obj_addr);
      target_in g0 g st0 st (v <: obj_addr)
    end

/// ---------------------------------------------------------------------------
/// The theorem
/// ---------------------------------------------------------------------------

let wf_after (g0 g: heap) (st0 st: pstate)
  : Lemma (requires sweep_ready g0 st0 /\ mark_done g0 /\ inv2 g0 st0 g st n_pages)
          (ensures well_formed_heap g)
  = reveal_opaque (`%well_formed_heap) well_formed_heap;
    R.part1_always g;
    part4_after g0 g st0 st;
    let closure (src: obj_addr) (j: nat)
      : Lemma (requires Seq.mem src (objects zero_addr g) /\ fields_constrained g src /\
                        j < U64.v (wosize_of_object src g) /\
                        U64.v src + j * 8 + 8 <= heap_size)
              (ensures (let v = read_word g (U64.uint_to_t (U64.v src + j * 8)) in
                        is_pointer v ==>
                        Seq.mem (resolve_object (v <: obj_addr) g) (objects zero_addr g) /\
                        infix_addr_wf g (objects zero_addr g) (v <: obj_addr)))
      = field_target g0 g st0 st src j
    in
    well_formed_heap_part2_3_from_resolved_field_closure g closure

/// **The swept heap is well formed.**  With `sweep_all_correct`: from the
/// state the mark leaves, the sweep ends with `pages_ok`, `well_formed_heap`
/// and every page swept.
let sweep_all_wf (g: heap) (st: pstate)
  : Lemma (requires sweep_ready g st /\ mark_done g)
          (ensures (let (g', st') = sweep_all g st in
                    well_formed_heap g' /\ pages_ok g' st' /\
                    (forall (j: nat{j < n_pages}). (entry st'.pm j).swept == true)))
  = sweep_all_inv2 g st;
    let (g', st') = sweep_all g st in
    wf_after g g' st st';
    sweep_all_correct g st

/// The same at the end of any run of steps (for a sweep driven step by step).
let sweep_end_wf (g0: heap) (st0: pstate) (g: heap) (st: pstate)
  : Lemma (requires sweep_ready g0 st0 /\ mark_done g0 /\ inv2 g0 st0 g st n_pages)
          (ensures well_formed_heap g)
  = wf_after g0 g st0 st
