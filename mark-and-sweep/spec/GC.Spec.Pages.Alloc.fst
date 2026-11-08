/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Alloc - the page allocator, and its correctness
/// ---------------------------------------------------------------------------
///
/// `alloc g st wz` allocates an object of wosize `wz`:
///   - a small block (`wz + 1 <= small_max`) takes a slot of its class
///     (`GC.Spec.Pages.Pool`);
///   - a large block takes the first listed block that fits, carving it
///     from the right (`GC.Spec.Pages.Large`), or else a new run of free
///     pages (`GC.Spec.Pages.NewRun`);
///   - otherwise there is no room, and nothing changes.
///
/// **`alloc_correct`** proves `alloc_meets alloc`, the statement of
/// docs/pages-allocator-proof-plan.md §2.2 (`GC.Spec.Pages.Theorems`).
/// `init_alloc_pre` and `init_alloc_succeeds` show it is not vacuous: the
/// empty heap of pages meets its precondition, and an allocation there
/// succeeds.

module GC.Spec.Pages.Alloc

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
open GC.Spec.Pages.Cells
open GC.Spec.Pages.Step
open GC.Spec.Pages.Theorems

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module Pool = GC.Spec.Pages.Pool
module LG = GC.Spec.Pages.Large
module NR = GC.Spec.Pages.NewRun
module Init = GC.Spec.Pages.Init
module Mark = GC.Spec.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The allocator
/// ---------------------------------------------------------------------------

let large_alloc (g: heap) (st: pstate) (wz: nat{wz < pow2 54}) : GTot (heap & pstate & U64.t) =
  let cs = walk g (large_head st) heap_words in
  match LG.split_fit g cs (wz + 1) with
  | Some (pre, c, post) -> LG.carve g st pre c wz
  | None ->
    let k = pages_for (wz + 1) in
    let i = NR.find_run st.pm k 0 in
    if i + k > n_pages then (g, st, 0UL)
    else NR.new_run g st i k wz

let alloc (g: heap) (st: pstate) (wz: nat) : GTot (heap & pstate & U64.t) =
  if wz + 1 >= pow2 54 then (g, st, 0UL)
  else if wz + 1 <= small_max then Pool.small_alloc g st wz
  else large_alloc g st wz

/// ---------------------------------------------------------------------------
/// Correctness
/// ---------------------------------------------------------------------------

/// No large block fits: every free listable block is too small, and no run
/// of free pages is long enough.
let large_oom (g: heap) (st: pstate) (wz: nat{wz < pow2 54})
  : Lemma (requires pages_ok g st /\ wz + 1 > small_max /\
                    None? (LG.split_fit g (walk g (large_head st) heap_words) (wz + 1)) /\
                    NR.find_run st.pm (pages_for (wz + 1)) 0 + pages_for (wz + 1) > n_pages)
          (ensures no_fit g st (wz + 1))
  = let cs = walk g (large_head st) heap_words in
    pages_ok_elim g st;
    large_ok_lview g st;
    LG.split_fit_none g cs (wz + 1);
    NR.find_run_spec st.pm (pages_for (wz + 1)) 0

let large_alloc_ok (g: heap) (st: pstate) (wz: nat{wz < pow2 54})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ wz + 1 > small_max)
          (ensures (let (g', st', obj) = large_alloc g st wz in alloc_ok g g' st st' wz obj))
  = let cs = walk g (large_head st) heap_words in
    params_ok ();
    cls_bounds 0;
    match LG.split_fit g cs (wz + 1) with
    | Some (pre, c, post) ->
      LG.split_fit_some g cs (wz + 1) pre c post;
      pages_ok_elim g st;
      large_ok_lview g st;
      LG.carve_ok g st pre c post wz
    | None ->
      let k = pages_for (wz + 1) in
      let i = NR.find_run st.pm k 0 in
      NR.find_run_spec st.pm k 0;
      if i + k > n_pages then large_oom g st wz
      else NR.new_run_ok g st i k wz

/// **The page allocator is correct.**
let alloc_ok_at (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok g st /\ well_formed_heap g)
          (ensures (let (g', st', obj) = alloc g st wz in alloc_ok g g' st st' wz obj))
  = if wz + 1 >= pow2 54 then ()
    else if wz + 1 <= small_max then Pool.small_alloc_ok g st wz
    else large_alloc_ok g st wz

let alloc_correct () : Lemma (alloc_meets alloc)
  = let aux (g: heap) (st: pstate) (wz: nat)
      : Lemma (pages_ok g st /\ well_formed_heap g ==>
               (let (g', st', obj) = alloc g st wz in alloc_ok g g' st st' wz obj))
      = FStar.Classical.move_requires (alloc_ok_at g st) wz
    in
    FStar.Classical.forall_intro_3 aux

/// ---------------------------------------------------------------------------
/// Vacuity
/// ---------------------------------------------------------------------------

/// Every block of the empty heap of pages is blue, with tag 0.
let init_hdr (g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr (Init.init_heap g)))
          (ensures is_blue x (Init.init_heap g) /\ tag_of_object x (Init.init_heap g) == 0UL)
  = let g' = Init.init_heap g in
    Init.init_all_blue g x;
    objects_steps_to g' zero_addr x;
    hd_address_spec x;
    steps_to_refl g' (U64.v zero_addr);
    Init.init_steps g 0 (U64.v (hd_address x));
    tag_of_object_spec x g';
    let h = U64.v (hd_address x) in
    FStar.Math.Lemmas.pow2_lt_compat 54 20;
    FStar.Math.Lemmas.pow2_lt_compat 64 20;
    eliminate exists (j': nat). 0 <= j' /\ j' <= n_pages /\ h == page_base j'
    with begin
      if j' < n_pages then begin
        Init.init_page g j';
        assert (hd_address x == Init.page_addr j');
        cls_bounds 0;
        makeHeader_getTag (U64.uint_to_t (page_wsize - 1)) Blue 0UL
      end else begin
        pages_end_bound ();
        page_base_aligned n_pages;
        assert (heap_size % 8 == 0);
        FStar.Math.Lemmas.lemma_mod_sub_distr heap_size pages_end 8;
        Init.tail_bound ();
        Init.init_tail g;
        assert (hd_address x == Init.tail_addr ());
        makeHeader_getTag (U64.uint_to_t (Init.tail_w - 1)) Blue 0UL
      end
    end

/// **Non-vacuity of the precondition**: the empty heap of pages meets it.
let init_alloc_pre (g: heap)
  : Lemma (pages_ok (Init.init_heap g) Init.init_state /\ well_formed_heap (Init.init_heap g))
  = let g' = Init.init_heap g in
    Init.init_pages_ok g;
    reveal_opaque (`%well_formed_heap) well_formed_heap;
    GC.Spec.Pages.Replace.part1_always g';
    let p4 (x: obj_addr) : Lemma (Seq.mem x (objects zero_addr g') ==> ~(is_infix x g'))
      = if Seq.mem x (objects zero_addr g') then begin
          init_hdr g x;
          is_infix_spec x g';
          infix_tag_val ()
        end
    in
    FStar.Classical.forall_intro p4;
    let closure (src: obj_addr) (j: nat)
      : Lemma (requires Seq.mem src (objects zero_addr g') /\ fields_constrained g' src /\
                        j < U64.v (wosize_of_object src g') /\
                        U64.v src + j * 8 + 8 <= heap_size)
              (ensures (let v = read_word g' (U64.uint_to_t (U64.v src + j * 8)) in
                        is_pointer v ==>
                        Seq.mem (resolve_object (v <: obj_addr) g') (objects zero_addr g') /\
                        infix_addr_wf g' (objects zero_addr g') (v <: obj_addr)))
      = init_hdr g src
    in
    well_formed_heap_part2_3_from_resolved_field_closure g' closure

/// **Non-vacuity of the result**: on the empty heap of pages, with at least
/// one page, allocating a small block succeeds.
let init_alloc_succeeds (g: heap) (wz: nat)
  : Lemma (requires n_pages > 0 /\ wz + 1 <= small_max)
          (ensures (let (_, _, obj) = alloc (Init.init_heap g) Init.init_state wz in obj =!= 0UL))
  = init_alloc_pre g;
    alloc_ok_at (Init.init_heap g) Init.init_state wz;
    params_ok ();
    FStar.Math.Lemmas.pow2_le_compat 54 20;
    assert ((entry Init.init_state.pm 0).kind == Free)

/// **Non-vacuity of the large path**: on the empty heap of pages, a large
/// block that fits in the pages is allocated.
let init_alloc_large_succeeds (g: heap) (wz: nat)
  : Lemma (requires wz + 1 > small_max /\ wz + 1 < pow2 54 /\ pages_for (wz + 1) <= n_pages)
          (ensures (let (_, _, obj) = alloc (Init.init_heap g) Init.init_state wz in obj =!= 0UL))
  = init_alloc_pre g;
    alloc_ok_at (Init.init_heap g) Init.init_state wz;
    assert (free_run Init.init_state.pm 0 (pages_for (wz + 1)))
