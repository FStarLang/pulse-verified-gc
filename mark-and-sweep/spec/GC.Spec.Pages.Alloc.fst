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
/// As OCaml's `caml_alloc_shr`, it writes the object's header and leaves
/// its fields as they were; the caller writes them.
///
/// **`alloc_correct`** proves `alloc_meets alloc`, the statement of
/// docs/pages-allocator-proof-plan.md §2.2 (`GC.Spec.Pages.Theorems`).  The
/// per-path proofs are about the heap the allocator would make if it
/// cleared the fields (`alloc_as true`, with `cleared_ok`); `alloc_ok_of`
/// takes them to the allocator's own heap, with `GC.Spec.Pages.Fill.fill_ok`
/// for the caller's writes.
///
/// `init_alloc_pre`, `init_alloc_succeeds` and `alloc_fill_exists` show it
/// is not vacuous: the empty heap of pages meets its precondition, an
/// allocation there succeeds, and the caller can always write the fields.

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
open GC.Spec.Pages.Frame
open GC.Spec.Pages.Replace
open GC.Spec.Pages.Cells
open GC.Spec.Pages.Blocks
open GC.Spec.Pages.Step
open GC.Spec.Pages.Theorems

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module Pool = GC.Spec.Pages.Pool
module LG = GC.Spec.Pages.Large
module NR = GC.Spec.Pages.NewRun
module Init = GC.Spec.Pages.Init
module F = GC.Spec.Pages.Fill
module Mark = GC.Spec.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The allocator
/// ---------------------------------------------------------------------------

/// `clr` says whether the new object's fields are cleared
/// (`GC.Spec.Pages.Blocks.put_obj_as`).
let large_alloc_as (clr: bool) (g: heap) (st: pstate) (wz: nat{wz < pow2 54})
  : GTot (heap & pstate & U64.t) =
  let cs = walk g (large_head st) heap_words in
  match LG.split_fit g cs (wz + 1) with
  | Some (pre, c, post) -> LG.carve_as clr g st pre c wz
  | None ->
    let k = pages_for (wz + 1) in
    let i = NR.find_run st.pm k 0 in
    if i + k > n_pages then (g, st, 0UL)
    else NR.new_run_as clr g st i k wz

let alloc_as (clr: bool) (g: heap) (st: pstate) (wz: nat) : GTot (heap & pstate & U64.t) =
  if wz + 1 >= pow2 54 then (g, st, 0UL)
  else if wz + 1 <= small_max then Pool.small_alloc_as clr g st wz
  else large_alloc_as clr g st wz

/// **The page allocator.**  It leaves the new object's fields as they were.
let alloc (g: heap) (st: pstate) (wz: nat) : GTot (heap & pstate & U64.t) =
  alloc_as false g st wz

/// ---------------------------------------------------------------------------
/// The heap with the fields cleared
/// ---------------------------------------------------------------------------

let large_alloc_clears (g: heap) (st: pstate) (wz: nat{wz < pow2 54})
  : Lemma (let (gr, sr, o) = large_alloc_as false g st wz in
           let (gc, sc, oc) = large_alloc_as true g st wz in
           sc == sr /\ oc == o /\ clears gr gc o wz)
  = let cs = walk g (large_head st) heap_words in
    match LG.split_fit g cs (wz + 1) with
    | Some (pre, c, post) -> LG.carve_clears g st pre c wz
    | None ->
      let k = pages_for (wz + 1) in
      let i = NR.find_run st.pm k 0 in
      if i + k > n_pages then () else NR.new_run_clears g st i k wz

/// The allocator's heap is the cleared one without the clearing.
let alloc_clears (g: heap) (st: pstate) (wz: nat{wz < pow2 54})
  : Lemma (let (gr, sr, o) = alloc_as false g st wz in
           let (gc, sc, oc) = alloc_as true g st wz in
           sc == sr /\ oc == o /\ clears gr gc o wz)
  = if wz + 1 >= pow2 54 then ()
    else if wz + 1 <= small_max then Pool.small_alloc_clears g st wz
    else large_alloc_clears g st wz

/// ---------------------------------------------------------------------------
/// Correctness of the cleared heap
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
          (ensures (let (g', st', obj) = large_alloc_as true g st wz in
                    cleared_ok g g' st st' wz obj))
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

let cleared_ok_at (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok g st /\ well_formed_heap g)
          (ensures (let (g', st', obj) = alloc_as true g st wz in cleared_ok g g' st st' wz obj))
  = if wz + 1 >= pow2 54 then ()
    else if wz + 1 <= small_max then Pool.small_alloc_ok g st wz
    else large_alloc_ok g st wz

/// ---------------------------------------------------------------------------
/// From the cleared heap to the allocator's
/// ---------------------------------------------------------------------------

/// The pages a run of unswept pages covers are kept.
let span_kept (g gc: heap) (st st': pstate) (j: nat{j < n_pages})
  : Lemma (requires map_ok st.pm /\ unswept_unchanged g gc st st' /\
                    (entry st.pm j).kind =!= LargeCont /\ not (entry st.pm j).swept)
          (ensures j + span st.pm j <= n_pages /\
                   kept_range g gc (page_base j) (page_base (j + span st.pm j)))
  = let n = span st.pm j in
    assert (run_ok st.pm j);
    page_base_mono j (j + n);
    let word (b: hp_addr)
      : Lemma (page_base j <= U64.v b /\ U64.v b < page_base (j + n) ==>
               read_word gc b == read_word g b)
      = if page_base j <= U64.v b && U64.v b < page_base (j + n) then begin
          page_of_spec (U64.v b);
          let m = page_of (U64.v b) in
          in_pages j n m (U64.v b);
          assert (not (entry st.pm m).swept);
          assert (page_kept g gc m)
        end
    in
    FStar.Classical.forall_intro word

/// A walk page is reached by the walk.
let reached (g: heap) (st: pstate) (j: nat{j < n_pages})
  : Lemma (requires pages_ok g st /\ (entry st.pm j).kind =!= LargeCont)
          (ensures steps_to g z (page_base j))
  = pages_ok_elim g st;
    walk_pages_reached g st.pm j

/// A field of the new object in a stretch of `gc` kept from `g`, from a
/// position both walks reach, would make the object an object of `g` that
/// is not free.
let fields_kept_at (g gc: heap) (x: obj_addr) (p e a: nat)
  : Lemma (requires kept_range g gc p e /\ steps_to g z p /\ steps_to gc z p /\ p % 8 == 0 /\
                    Seq.mem x (objects zero_addr gc) /\ ~(is_blue x gc) /\
                    ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                    p <= a /\ a < e /\ U64.v x <= a /\ a < F.fields_end gc x)
          (ensures False)
  = let h = U64.v x - 8 in
    F.walk_out gc x p;
    assert (p <= h);
    hd_address_spec x;
    obj_iff gc x;
    hdr_obj gc x;
    if p = h then steps_to_refl gc h
    else steps_to_det gc z p h;
    steps_to_frame g gc p h;
    steps_to_trans g z p h;
    kept_hdr g gc p e h;
    obj_iff g x;
    hdr_obj g x;
    assert (read_word gc (hd_address x) == read_word g (hd_address x));
    color_of_header_eq x g gc

/// The same, from the walk page `j` of unswept pages.
let fields_swept_at (g gc: heap) (st st': pstate) (x: obj_addr) (j: nat{j < n_pages}) (a: nat)
  : Lemma (requires pages_ok g st /\ pages_ok gc st' /\ map_ok st.pm /\
                    unswept_unchanged g gc st st' /\
                    Seq.mem x (objects zero_addr gc) /\ ~(is_blue x gc) /\
                    ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                    (entry st.pm j).kind =!= LargeCont /\ not (entry st.pm j).swept /\
                    page_base j <= a /\ a < page_base (j + span st.pm j) /\
                    U64.v x <= a /\ a < F.fields_end gc x)
          (ensures False)
  = span_kept g gc st st' j;
    reached g st j;
    reached gc st' j;
    page_base_aligned j;
    fields_kept_at g gc x (page_base j) (page_base (j + span st.pm j)) a

/// So the fields of the new object lie in swept pages.
let fields_swept (g gc: heap) (st st': pstate) (x: obj_addr) (i: nat{i < n_pages}) (a: nat)
  : Lemma (requires pages_ok g st /\ pages_ok gc st' /\ unswept_unchanged g gc st st' /\
                    Seq.mem x (objects zero_addr gc) /\ ~(is_blue x gc) /\
                    ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                    not (entry st.pm i).swept /\
                    page_base i <= a /\ a < page_base (i + 1) /\
                    U64.v x <= a /\ a < F.fields_end gc x)
          (ensures False)
  = pages_ok_elim g st;
    let pm = st.pm in
    assert (map_ok pm);
    assert (free_ok pm i /\ cont_ok pm i);
    match (entry pm i).kind with
    | LargeCont ->
      eliminate exists (h: nat{h < n_pages}). h < i /\ in_run pm h i
      with begin
        assert (run_ok pm h);
        let n = run_len (entry pm h).kind in
        page_base_mono h i;
        page_base_mono (i + 1) (h + n);
        fields_swept_at g gc st st' x h a
      end
    | _ ->
      assert (run_ok pm i);
      page_base_mono (i + 1) (i + span pm i);
      fields_swept_at g gc st st' x i a

let unswept_raw (g gr gc: heap) (st st': pstate) (x: obj_addr)
  : Lemma (requires pages_ok g st /\ pages_ok gc st' /\ unswept_unchanged g gc st st' /\
                    Seq.mem x (objects zero_addr gc) /\ ~(is_blue x gc) /\
                    ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                    (forall (a: hp_addr). U64.v a < U64.v x \/ U64.v a >= F.fields_end gc x ==>
                       read_word gr a == read_word gc a))
          (ensures unswept_unchanged g gr st st')
  = let aux (i: nat{i < n_pages})
      : Lemma (not (entry st.pm i).swept ==> entry st'.pm i == entry st.pm i /\ page_kept g gr i)
      = if not (entry st.pm i).swept then begin
          let word (a: hp_addr)
            : Lemma (page_base i <= U64.v a /\ U64.v a < page_base (i + 1) ==>
                     read_word gr a == read_word g a)
            = if page_base i <= U64.v a && U64.v a < page_base (i + 1) &&
                 U64.v x <= U64.v a && U64.v a < F.fields_end gc x
              then fields_swept g gc st st' x i (U64.v a)
          in
          FStar.Classical.forall_intro word
        end
    in
    FStar.Classical.forall_intro aux

let others_raw (g gr gc: heap) (x: obj_addr)
  : Lemma (requires others_unchanged g gc /\ Seq.mem x (objects zero_addr gc) /\
                    ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                    F.fctx gc gr x)
          (ensures others_unchanged g gr)
  = let aux (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g) /\ ~(is_blue y g))
              (ensures Seq.mem y (objects zero_addr gr) /\
                       read_word gr (hd_address y) == read_word g (hd_address y) /\
                       (forall (b: hp_addr). U64.v y <= U64.v b /\
                          U64.v b < U64.v y + U64.v (wosize_of_object y g) * 8 ==>
                          read_word gr b == read_word g b))
      = F.obj_same gc gr x y;
        F.other_apart gc x y;
        hd_address_spec y;
        wosize_of_object_spec y g;
        wosize_of_object_spec y gc
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// The new object of the cleared heap is white with tag 0, so not a closure.
let new_obj_facts (gr gc: heap) (x: obj_addr) (wz: nat{wz < pow2 54})
  : Lemma (requires clears gr gc x wz /\ Seq.mem x (objects zero_addr gc))
          (ensures read_word gr (hd_address x) == read_word gc (hd_address x) /\
                   is_white x gc /\ ~(is_blue x gc) /\ ~(is_closure x gc))
  = hd_address_spec x;
    obj_iff gc x;
    hdr_obj gc x;
    zeros_read gr (U64.v x) wz (hd_address x);
    ohdr_spec wz;
    assert (hdr gc (U64.v x - 8) == hdr gr (U64.v x - 8));
    is_white_iff x gc;
    is_blue_iff x gc;
    is_closure_spec x gc;
    closure_tag_val ()

/// **The allocator's heap, from the cleared one.**
#push-options "--z3rlimit 40"
let alloc_ok_of (g gr gc: heap) (st st': pstate) (wz: nat{wz < pow2 54}) (obj: U64.t)
  : Lemma (requires pages_ok g st /\ cleared_ok g gc st st' wz obj /\ clears gr gc obj wz)
          (ensures alloc_ok g gr st st' wz obj)
  = if obj <> 0UL then begin
      let x : obj_addr = obj in
      new_obj_facts gr gc x wz;
      let outside (a: hp_addr)
        : Lemma (U64.v a < U64.v x \/ U64.v a >= F.fields_end gc x ==> read_word gr a == read_word gc a)
        = zeros_read gr (U64.v x) wz a
      in
      FStar.Classical.forall_intro outside;
      assert (F.fctx gc gr x);
      F.obj_same gc gr x x;
      color_of_header_eq x gr gc;
      wosize_of_object_spec x gr;
      wosize_of_object_spec x gc;
      others_raw g gr gc x;
      unswept_raw g gr gc st st' x;
      let fill (g'': heap)
        : Lemma (requires fields_written gr g'' x)
                (ensures pages_ok g'' st' /\ well_formed_heap g'')
        = F.fill_ok gc g'' st' x
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires fill)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Correctness
/// ---------------------------------------------------------------------------

/// **The page allocator is correct.**
let alloc_ok_at (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok g st /\ well_formed_heap g)
          (ensures (let (g', st', obj) = alloc g st wz in alloc_ok g g' st st' wz obj))
  = if wz + 1 >= pow2 54 then ()
    else begin
      cleared_ok_at g st wz;
      alloc_clears g st wz;
      let (gr, _, obj) = alloc_as false g st wz in
      let (gc, st', _) = alloc_as true g st wz in
      alloc_ok_of g gr gc st st' wz obj
    end

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

/// **Non-vacuity of the caller's part**: the caller can always write the
/// fields (clearing them will do), and then the heap is valid.
let alloc_fill_exists (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok g st /\ well_formed_heap g)
          (ensures (let (g', st', obj) = alloc g st wz in
                    obj =!= 0UL ==>
                    U64.v obj >= 8 /\ U64.v obj < heap_size /\ U64.v obj % 8 == 0 /\
                    (let x : obj_addr = obj in
                     let g'' = zeros g' (U64.v x) wz in
                     fields_written g' g'' x /\ pages_ok g'' st' /\ well_formed_heap g'')))
  = alloc_ok_at g st wz;
    match alloc g st wz with
    | (g', st', obj) ->
      if obj <> 0UL then begin
        assert (alloc_ok g g' st st' wz obj);
        F.cleared_written g' (obj <: obj_addr)
      end

/// On the empty heap of pages, a small allocation succeeds and its fields
/// can be written.
let init_alloc_filled (g: heap) (wz: nat)
  : Lemma (requires n_pages > 0 /\ wz + 1 <= small_max)
          (ensures (let (g', st', obj) = alloc (Init.init_heap g) Init.init_state wz in
                    obj =!= 0UL /\
                    U64.v obj >= 8 /\ U64.v obj < heap_size /\ U64.v obj % 8 == 0 /\
                    (let x : obj_addr = obj in
                     pages_ok (zeros g' (U64.v x) wz) st')))
  = init_alloc_succeeds g wz;
    init_alloc_pre g;
    alloc_fill_exists (Init.init_heap g) Init.init_state wz
