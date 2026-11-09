/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.AllocPhase - allocation in any colour, from pages_ok up to colours
/// ---------------------------------------------------------------------------
///
/// The page allocator for a collector that may be marking:
///
///   - **`pages_ok_mc g st`**: `pages_ok` up to the colours of live objects.
///     `g` is well formed, and whitening some objects of `g` that are not
///     free gives a heap that satisfies `pages_ok`.  `pages_ok` with
///     `well_formed_heap` implies it (`mc_of_ok`).
///   - **`alloc_col col`**: the allocator, with the new object's header of
///     colour `col`.  `alloc_col White` is `alloc` (`alloc_col_white`).
///   - **`alloc_col_correct`**: from `pages_ok_mc`, `alloc_col col` meets
///     `alloc_ok_col col`, which is `alloc_ok` (`GC.Spec.Pages.Theorems`)
///     with the new object of colour `col` and `pages_ok_mc` in place of
///     `pages_ok /\ well_formed_heap` for the heap the caller makes.  Every
///     other clause is `alloc_ok`'s: in particular every live object keeps
///     its header exactly, colour included, and unswept pages are left as
///     they were.
///
/// The proof runs the allocator on the whitened heap, where `alloc_correct`
/// applies, and carries the result back with `GC.Spec.Pages.Recolour`.

module GC.Spec.Pages.AllocPhase

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
open GC.Spec.Pages.Blocks
open GC.Spec.Pages.Theorems
open GC.Spec.Pages.Recolour
open GC.Spec.Pages.ColourFacts

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module HE = GC.Gen.HeapExtensional
module A = GC.Spec.Pages.Alloc
module F = GC.Spec.Pages.Fill
module R = GC.Spec.Pages.Replace
module FR = GC.Spec.Pages.Frame

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The invariant up to colours
/// ---------------------------------------------------------------------------

let pages_ok_mc (g: heap) (st: pstate) : prop =
  well_formed_heap g /\
  (exists (ys: list obj_addr). live_list g ys /\ pages_ok (whiten g ys) st)

#push-options "--fuel 1"
let live_list_nil (g: heap) : Lemma (live_list g []) = ()
#pop-options

let mc_of_ok (g: heap) (st: pstate)
  : Lemma (requires pages_ok g st /\ well_formed_heap g) (ensures pages_ok_mc g st)
  = whiten_nil g;
    live_list_nil g

let mc_ctx (g: heap) (ys: list obj_addr) (st: pstate)
  : Lemma (requires well_formed_heap g /\ live_list g ys /\ pages_ok (whiten g ys) st)
          (ensures ctx g ys ys st /\ well_formed_heap (whiten g ys))
  = whiten_facts g ys;
    whiten_wh g ys

/// ---------------------------------------------------------------------------
/// The allocator in a colour
/// ---------------------------------------------------------------------------

/// The header of `o` recoloured `col`.
let recolour (g: heap) (o: U64.t) (col: color) : GTot heap =
  if U64.v o >= 8 then wr g (U64.v o - 8) (colorHeader (hdr g (U64.v o - 8)) col) else g

let alloc_col (col: color) (g: heap) (st: pstate) (wz: nat) : GTot (heap & pstate & U64.t) =
  let (g', st', o) = A.alloc g st wz in
  if o = 0UL then (g', st', o) else (recolour g' o col, st', o)

/// `alloc_ok` with the new object of colour `col`, from the invariant up to
/// colours.
let alloc_ok_col (col: color) (g g': heap) (st st': pstate) (wz: nat) (obj: U64.t) : prop =
  (obj == 0UL ==> g' == g /\ st' == st /\ (wz + 1 < pow2 54 ==> no_fit g st (wz + 1))) /\
  (obj =!= 0UL ==>
     U64.v obj >= 8 /\ U64.v obj < heap_size /\ U64.v obj % 8 == 0 /\
     (let x : obj_addr = obj in
      Seq.mem x (objects zero_addr g') /\
      U64.v (wosize_of_object x g') == wz /\
      color_of_object x g' == col /\
      ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
      (forall (g'': heap). fields_written g' g'' x ==> pages_ok_mc g'' st')) /\
     others_unchanged g g' /\
     unswept_unchanged g g' st st')

/// ---------------------------------------------------------------------------
/// Every word the whitened run keeps, the real run keeps
/// ---------------------------------------------------------------------------

#push-options "--fuel 2"
let sub_one (y: obj_addr) (ys: list obj_addr) : Lemma (requires L.mem y ys) (ensures sub [y] ys /\ L.mem y [y]) = ()
#pop-options

/// The allocator in `g` is the allocator in `whiten g ys`, unwhitened.
let alloc_whitened (g: heap) (ys: list obj_addr) (st: pstate) (wz: nat)
  : Lemma (requires ctx g ys ys st)
          (ensures (let (g', st', o) = A.alloc g st wz in
                    A.alloc (whiten g ys) st wz == (whiten g' ys, st', o)))
  = alloc_paint g ys ys White st wz

/// A header of `ys` the whitened run keeps is kept, colour included: the
/// allocator also commutes with painting that object its own colour.
let kept_hdr_y (g: heap) (ys: list obj_addr) (st: pstate) (wz: nat) (y: obj_addr)
  : Lemma (requires ctx g ys ys st /\ L.mem y ys /\
                    (let (g', _, _) = A.alloc g st wz in
                     hdr (whiten g' ys) (hx y) == hdr (whiten g ys) (hx y)))
          (ensures (let (g', _, _) = A.alloc g st wz in hdr g' (hx y) == hdr g (hx y)))
  = let (g', st', o) = A.alloc g st wz in
    let cy = color_at g (hx y) in
    sub_one y ys;
    alloc_paint g ys [y] cy st wz;
    paint_own g y;
    assert (g' == paint g' [y] cy);
    paint_on g' [y] cy y;
    paint_on g' ys White y;
    paint_on g ys White y;
    colorHeader_twice (hdr g' (hx y)) White cy;
    colorHeader_twice (hdr g (hx y)) White cy;
    colorHeader_same (hdr g (hx y)) cy

/// Every word the whitened run keeps is kept.
let kept_word (g: heap) (ys: list obj_addr) (st: pstate) (wz: nat) (a: hp_addr)
  : Lemma (requires ctx g ys ys st /\
                    (let (g', _, _) = A.alloc g st wz in
                     read_word (whiten g' ys) a == read_word (whiten g ys) a))
          (ensures (let (g', _, _) = A.alloc g st wz in read_word g' a == read_word g a))
  = let (g', st', o) = A.alloc g st wz in
    if FStar.IndefiniteDescription.strong_excluded_middle (avoid ys (U64.v a)) then begin
      paint_off g' ys White a;
      paint_off g ys White a
    end
    else begin
      eliminate exists (y: obj_addr). L.mem y ys /\ hx y == U64.v a
      with begin
        assert (hdr g' (hx y) == read_word g' a);
        assert (hdr g (hx y) == read_word g a);
        kept_hdr_y g ys st wz y
      end
    end

/// ---------------------------------------------------------------------------
/// The new object's header lies in a swept page
/// ---------------------------------------------------------------------------

/// The header of the new object in a stretch of `gc` kept from `g`, from a
/// position both walks reach, would make it an object of `g` that is not
/// free (as `GC.Spec.Pages.Alloc.fields_kept_at`, for the header).
let hdr_kept_at (g gc: heap) (x: obj_addr) (p e: nat)
  : Lemma (requires FR.kept_range g gc p e /\ steps_to g R.z p /\ steps_to gc R.z p /\ p % 8 == 0 /\
                    Seq.mem x (objects zero_addr gc) /\ ~(is_blue x gc) /\
                    ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                    p <= hx x /\ hx x < e)
          (ensures False)
  = let h = hx x in
    hd_address_spec x;
    R.obj_iff gc x;
    R.hdr_obj gc x;
    if p = h then steps_to_refl gc h
    else R.steps_to_det gc R.z p h;
    steps_to_frame g gc p h;
    steps_to_trans g R.z p h;
    FR.kept_hdr g gc p e h;
    R.obj_iff g x;
    R.hdr_obj g x;
    assert (read_word gc (hd_address x) == read_word g (hd_address x));
    color_of_header_eq x g gc

let hdr_swept_at (g gc: heap) (st st': pstate) (x: obj_addr) (j: nat{j < n_pages})
  : Lemma (requires pages_ok g st /\ pages_ok gc st' /\ map_ok st.pm /\
                    unswept_unchanged g gc st st' /\
                    Seq.mem x (objects zero_addr gc) /\ ~(is_blue x gc) /\
                    ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                    (entry st.pm j).kind =!= LargeCont /\ not (entry st.pm j).swept /\
                    page_base j <= hx x /\ hx x < page_base (j + span st.pm j))
          (ensures False)
  = A.span_kept g gc st st' j;
    A.reached g st j;
    A.reached gc st' j;
    page_base_aligned j;
    hdr_kept_at g gc x (page_base j) (page_base (j + span st.pm j))

let hdr_swept (g gc: heap) (st st': pstate) (x: obj_addr) (i: nat{i < n_pages})
  : Lemma (requires pages_ok g st /\ pages_ok gc st' /\ unswept_unchanged g gc st st' /\
                    Seq.mem x (objects zero_addr gc) /\ ~(is_blue x gc) /\
                    ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                    not (entry st.pm i).swept /\
                    page_base i <= hx x /\ hx x < page_base (i + 1))
          (ensures False)
  = GC.Spec.Pages.Step.pages_ok_elim g st;
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
        hdr_swept_at g gc st st' x h
      end
    | _ ->
      assert (run_ok pm i);
      page_base_mono (i + 1) (i + span pm i);
      hdr_swept_at g gc st st' x i

/// **Only swept pages are used**: the new object's header is not in an
/// unswept page.  (Its fields are not either: `GC.Spec.Pages.Alloc.fields_swept`.)
let new_hdr_swept (g: heap) (st: pstate) (wz: nat) (i: nat{i < n_pages})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ not (entry st.pm i).swept)
          (ensures (let (_, _, o) = A.alloc g st wz in
                    o =!= 0UL ==> U64.v o >= 8 /\ ~(page_base i <= U64.v o - 8 /\ U64.v o - 8 < page_base (i + 1))))
  = let (g', st', o) = A.alloc g st wz in
    if o = 0UL then ()
    else if wz + 1 >= pow2 54 then ()
    else begin
      A.alloc_clears g st wz;
      A.cleared_ok_at g st wz;
      let (gc, sc, oc) = A.alloc_as true g st wz in
      let x : obj_addr = o in
      is_white_iff x gc;
      is_blue_iff x gc;
      if page_base i <= hx x && hx x < page_base (i + 1) then hdr_swept g gc st st' x i
    end

/// ---------------------------------------------------------------------------
/// The run on the whitened heap
/// ---------------------------------------------------------------------------

/// What the allocator's run on `whiten g ys` gives.
let base (g: heap) (ys: list obj_addr) (st: pstate) (wz: nat)
  : Lemma (requires well_formed_heap g /\ live_list g ys /\ pages_ok (whiten g ys) st)
          (ensures (let (g', st', o) = A.alloc g st wz in
                    let gw = whiten g ys in
                    ctx g ys ys st /\ well_formed_heap gw /\
                    A.alloc gw st wz == (whiten g' ys, st', o) /\
                    alloc_ok gw (whiten g' ys) st st' wz o /\
                    objects zero_addr gw == objects zero_addr g /\
                    (forall (y: obj_addr). is_blue y gw <==> is_blue y g) /\
                    objects zero_addr (whiten g' ys) == objects zero_addr g'))
  = let (g', st', o) = A.alloc g st wz in
    mc_ctx g ys st;
    whiten_facts g ys;
    alloc_whitened g ys st wz;
    A.alloc_ok_at (whiten g ys) st wz;
    whiten_objects g' ys

/// A free block of `g` is not one of `ys`.
let blue_not_in (g: heap) (ys: list obj_addr) (y: obj_addr)
  : Lemma (requires live_list g ys /\ is_blue y g) (ensures avoid ys (hx y))
  = ()

/// `no_fit` does not read the colours of live objects.
let no_fit_back (g: heap) (ys: list obj_addr) (st: pstate) (w: pos)
  : Lemma (requires live_list g ys /\ no_fit (whiten g ys) st w)
          (ensures no_fit g st w)
  = whiten_facts g ys;
    let one (y: obj_addr)
      : Lemma (Seq.mem y (objects zero_addr g) /\ is_blue y g ==> whsize (whiten g ys) y == whsize g y)
      = if FStar.IndefiniteDescription.strong_excluded_middle (is_blue y g) then begin
          blue_not_in g ys y;
          whsize_paint g ys White y
        end
    in
    FStar.Classical.forall_intro one

/// No room: nothing changes.
let zero_case (g: heap) (ys: list obj_addr) (st: pstate) (wz: nat)
  : Lemma (requires well_formed_heap g /\ live_list g ys /\ pages_ok (whiten g ys) st /\
                    (let (_, _, o) = A.alloc g st wz in o == 0UL))
          (ensures (let (g', st', _) = A.alloc g st wz in
                    g' == g /\ st' == st /\ (wz + 1 < pow2 54 ==> no_fit g st (wz + 1))))
  = let (g', st', o) = A.alloc g st wz in
    base g ys st wz;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (kept_word g ys st wz));
    let aux (b: nat) : Lemma (b < heap_size /\ b % 8 == 0 ==>
                              read_word g' (U64.uint_to_t b) == read_word g (U64.uint_to_t b))
      = ()
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext g' g;
    if wz + 1 < pow2 54 then no_fit_back g ys st (wz + 1)

/// ---------------------------------------------------------------------------
/// The new object
/// ---------------------------------------------------------------------------

let recolour_eq (g: heap) (x: obj_addr) (col: color)
  : Lemma (requires col <> Blue)
          (ensures recolour g (x <: U64.t) col == set_object_color x g col)
  = hd_address_spec x;
    R.hdr_obj g x;
    sc_eq g x col;
    assert (mk_hp_addr (hx x) == hd_address x)

/// The new object, in the real heap before and after recolouring.
let new_facts (g: heap) (ys: list obj_addr) (st: pstate) (wz: nat) (col: color)
  : Lemma (requires well_formed_heap g /\ live_list g ys /\ pages_ok (whiten g ys) st /\ col <> Blue /\
                    (let (_, _, o) = A.alloc g st wz in o =!= 0UL))
          (ensures (let (g', st', o) = A.alloc g st wz in
                    U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                    (let x : obj_addr = o in
                     let gc = recolour g' o col in
                     avoid ys (hx x) /\
                     hdr g' (hx x) == hdr (whiten g' ys) (hx x) /\
                     color_at (whiten g' ys) (hx x) == White /\
                     gc == set_object_color x g' col /\
                     Seq.mem x (objects zero_addr g') /\
                     objects zero_addr gc == objects zero_addr g' /\
                     Seq.mem x (objects zero_addr gc) /\
                     U64.v (wosize_of_object x g') == wz /\
                     U64.v (wosize_of_object x gc) == wz /\
                     color_of_object x gc == col /\
                     ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)))))
  = let (g', st', o) = A.alloc g st wz in
    base g ys st wz;
    let gw' = whiten g' ys in
    let x : obj_addr = o in
    let one (z: obj_addr) : Lemma (L.mem z ys ==> hx z <> hx x)
      = if L.mem z ys && hx z = hx x then U64.v_inj z x
    in
    FStar.Classical.forall_intro one;
    paint_hdr g' ys White (hx x);
    R.hdr_obj g' x;
    R.hdr_obj gw' x;
    is_white_iff x gw';
    recolour_eq g' x col;
    color_change_preserves_objects g' x col;
    color_preserves_wosize x g' col;
    color_of_object_spec x (set_object_color x g' col);
    hd_address_spec x;
    sc_eq g' x col;
    read_write_same g' (hd_address x) (colorHeader (read_word g' (hd_address x)) col);
    colorHeader_getColor (read_word g' (hd_address x)) col

/// ---------------------------------------------------------------------------
/// Everything else is kept
/// ---------------------------------------------------------------------------

/// Whitening keeps an object's wosize.
let whiten_wosize (g: heap) (ys: list obj_addr) (y: obj_addr)
  : Lemma (wosize_of_object y (whiten g ys) == wosize_of_object y g)
  = hd_address_spec y;
    hx_word y;
    paint_read g ys White (hd_address y);
    colorHeader_preserves_wosize (read_word g (hd_address y)) White;
    wosize_of_object_spec y g;
    wosize_of_object_spec y (whiten g ys)

/// One live object of `g` is kept in the recoloured heap.
let other_kept (g: heap) (ys: list obj_addr) (st: pstate) (wz: nat) (col: color) (y: obj_addr)
  : Lemma (requires well_formed_heap g /\ live_list g ys /\ pages_ok (whiten g ys) st /\ col <> Blue /\
                    (let (_, _, o) = A.alloc g st wz in o =!= 0UL) /\
                    Seq.mem y (objects zero_addr g) /\ ~(is_blue y g))
          (ensures (let (g', _, o) = A.alloc g st wz in
                    let gc = recolour g' o col in
                    Seq.mem y (objects zero_addr gc) /\
                    read_word gc (hd_address y) == read_word g (hd_address y) /\
                    (forall (b: hp_addr). U64.v y <= U64.v b /\ U64.v b < U64.v y + U64.v (wosize_of_object y g) * 8 ==>
                       read_word gc b == read_word g b)))
  = let (g', st', o) = A.alloc g st wz in
    base g ys st wz;
    new_facts g ys st wz col;
    let gw = whiten g ys in
    let gw' = whiten g' ys in
    let x : obj_addr = o in
    let gc = recolour g' o col in
    assert (others_unchanged gw gw');
    assert (y <> x);
    hd_address_spec y;
    hd_address_spec x;
    whiten_wosize g ys y;
    kept_word g ys st wz (hd_address y);
    R.hdr_obj g' y;
    R.hdr_obj g y;
    wr_read g' (hx x) (colorHeader (hdr g' (hx x)) col) (hd_address y);
    R.obj_iff g' x;
    F.walk_out g' y (hx x);
    let field (b: hp_addr)
      : Lemma (U64.v y <= U64.v b /\ U64.v b < U64.v y + U64.v (wosize_of_object y g) * 8 ==>
               read_word gc b == read_word g b)
      = if U64.v y <= U64.v b && U64.v b < U64.v y + U64.v (wosize_of_object y g) * 8 then begin
          kept_word g ys st wz b;
          wr_read g' (hx x) (colorHeader (hdr g' (hx x)) col) b
        end
    in
    FStar.Classical.forall_intro field

let others_kept (g: heap) (ys: list obj_addr) (st: pstate) (wz: nat) (col: color)
  : Lemma (requires well_formed_heap g /\ live_list g ys /\ pages_ok (whiten g ys) st /\ col <> Blue /\
                    (let (_, _, o) = A.alloc g st wz in o =!= 0UL))
          (ensures (let (g', _, o) = A.alloc g st wz in others_unchanged g (recolour g' o col)))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (other_kept g ys st wz col))

/// Unswept pages and their entries are kept.
let unswept_kept (g: heap) (ys: list obj_addr) (st: pstate) (wz: nat) (col: color)
  : Lemma (requires well_formed_heap g /\ live_list g ys /\ pages_ok (whiten g ys) st /\ col <> Blue /\
                    (let (_, _, o) = A.alloc g st wz in o =!= 0UL))
          (ensures (let (g', st', o) = A.alloc g st wz in unswept_unchanged g (recolour g' o col) st st'))
  = let (g', st', o) = A.alloc g st wz in
    base g ys st wz;
    new_facts g ys st wz col;
    let gw = whiten g ys in
    let x : obj_addr = o in
    let gc = recolour g' o col in
    let page (i: nat{i < n_pages})
      : Lemma (not (entry st.pm i).swept ==> entry st'.pm i == entry st.pm i /\ page_kept g gc i)
      = if not (entry st.pm i).swept then begin
          assert (page_kept gw (whiten g' ys) i);
          new_hdr_swept gw st wz i;
          let word (a: hp_addr)
            : Lemma (page_base i <= U64.v a /\ U64.v a < page_base (i + 1) ==> read_word gc a == read_word g a)
            = if page_base i <= U64.v a && U64.v a < page_base (i + 1) then begin
                kept_word g ys st wz a;
                wr_read g' (hx x) (colorHeader (hdr g' (hx x)) col) a
              end
          in
          FStar.Classical.forall_intro word
        end
    in
    FStar.Classical.forall_intro page

/// ---------------------------------------------------------------------------
/// The caller's writes
/// ---------------------------------------------------------------------------

/// The context of the caller's writes: `gc` is the allocator's heap, `g''`
/// the heap after the caller wrote the fields of `x`.
let fill_ctx (g: heap) (ys: list obj_addr) (st: pstate) (wz: nat) (col: color) (g'': heap) : prop =
  well_formed_heap g /\ live_list g ys /\ pages_ok (whiten g ys) st /\ col <> Blue /\
  (let (g', _, o) = A.alloc g st wz in
   o =!= 0UL /\ U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
   fields_written (recolour g' o col) g'' (o <: obj_addr))

/// A word outside the fields: the whitened heaps agree.
#push-options "--fuel 1"
let outside_word (g: heap) (ys: list obj_addr) (st: pstate) (wz: nat) (col: color) (g'': heap)
                 (a: hp_addr)
  : Lemma (requires fill_ctx g ys st wz col g'' /\
                    (let (g', _, o) = A.alloc g st wz in
                     let x : obj_addr = o in
                     (U64.v a < U64.v x \/ U64.v a >= U64.v x + U64.v (wosize_of_object x (recolour g' o col)) * 8)))
          (ensures (let (g', _, o) = A.alloc g st wz in
                    read_word (whiten g'' ((o <: obj_addr) :: ys)) a == read_word (whiten g' ys) a))
  = let (g', st', o) = A.alloc g st wz in
    let x : obj_addr = o in
    let gc = recolour g' o col in
    new_facts g ys st wz col;
    let zs = x :: ys in
    assert (read_word g'' a == read_word gc a);
    paint_read g'' zs White a;
    paint_read g' ys White a;
    hx_word x;
    assert (gc == wr g' (hx x) (colorHeader (hdr g' (hx x)) col));
    wr_read g' (hx x) (colorHeader (hdr g' (hx x)) col) a;
    if U64.v a = hx x then begin
      assert (hdr g' (hx x) == read_word g' a);
      assert (~(avoid zs (U64.v a)));
      assert (avoid ys (U64.v a));
      colorHeader_twice (read_word g' a) col White;
      colorHeader_same (read_word g' a) White
    end
    else begin
      assert (read_word gc a == read_word g' a);
      if FStar.IndefiniteDescription.strong_excluded_middle (avoid ys (U64.v a)) then
        assert (avoid zs (U64.v a))
      else
        assert (~(avoid zs (U64.v a)))
    end
#pop-options

/// No header of `zs`, objects of `g''`, lies in the fields of `x`.
let inside_avoid (g'': heap) (x: obj_addr) (zs: list obj_addr) (a: nat)
  : Lemma (requires Seq.mem x (objects zero_addr g'') /\
                    (forall (z: obj_addr). L.mem z zs ==> Seq.mem z (objects zero_addr g'')) /\
                    U64.v x <= a /\ a < F.fields_end g'' x)
          (ensures avoid zs a)
  = let one (z: obj_addr) : Lemma (L.mem z zs ==> hx z <> a)
      = if L.mem z zs then begin
          R.obj_iff g'' z;
          F.walk_out g'' x (hx z)
        end
    in
    FStar.Classical.forall_intro one

#push-options "--fuel 1"
let live_cons (g: heap) (x: obj_addr) (ys: list obj_addr)
  : Lemma (requires live_list g ys /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))
          (ensures live_list g (x :: ys))
  = ()
#pop-options

let fill_mc (g: heap) (ys: list obj_addr) (st: pstate) (wz: nat) (col: color) (g'': heap)
  : Lemma (requires fill_ctx g ys st wz col g'')
          (ensures (let (_, st', _) = A.alloc g st wz in pages_ok_mc g'' st'))
  = let (g', st', o) = A.alloc g st wz in
    let x : obj_addr = o in
    let gc = recolour g' o col in
    base g ys st wz;
    new_facts g ys st wz col;
    others_kept g ys st wz col;
    let gw' = whiten g' ys in
    let zs = x :: ys in
    (* g'' is gc but for the fields of x *)
    assert (F.fctx gc g'' x);
    FStar.Classical.forall_intro (F.obj_same gc g'' x);
    R.hdr_obj gc x;
    R.hdr_obj g'' x;
    color_of_header_eq x gc g'';
    is_blue_iff x g'';
    let live_y (y: obj_addr) : Lemma (L.mem y ys ==> Seq.mem y (objects zero_addr g'') /\ ~(is_blue y g''))
      = if L.mem y ys then color_of_header_eq y g g''
    in
    FStar.Classical.forall_intro live_y;
    live_cons g'' x ys;
    whiten_facts g'' zs;
    let gw'' = whiten g'' zs in
    (* the whitened heaps are related by a field write *)
    wosize_of_object_spec x gc;
    wosize_of_object_spec x g'';
    FStar.Classical.forall_intro (FStar.Classical.move_requires (outside_word g ys st wz col g''));
    let inside (a: hp_addr)
      : Lemma (U64.v x <= U64.v a /\ U64.v a < U64.v x + U64.v (wosize_of_object x gw') * 8 ==>
               field_ok gw'' (read_word gw'' a))
      = if U64.v x <= U64.v a && U64.v a < U64.v x + U64.v (wosize_of_object x gw') * 8 then begin
          inside_avoid g'' x zs (U64.v a);
          paint_off g'' zs White a
        end
    in
    FStar.Classical.forall_intro inside;
    assert (fields_written gw' gw'' x);
    assert (pages_ok gw'' st' /\ well_formed_heap gw'')

/// ---------------------------------------------------------------------------
/// The theorem
/// ---------------------------------------------------------------------------

let alloc_col_ys (col: color) (g: heap) (ys: list obj_addr) (st: pstate) (wz: nat)
  : Lemma (requires well_formed_heap g /\ live_list g ys /\ pages_ok (whiten g ys) st /\ col <> Blue)
          (ensures (let (g', st', o) = alloc_col col g st wz in alloc_ok_col col g g' st st' wz o))
  = let (g', st', o) = A.alloc g st wz in
    if o = 0UL then zero_case g ys st wz
    else begin
      new_facts g ys st wz col;
      others_kept g ys st wz col;
      unswept_kept g ys st wz col;
      let x : obj_addr = o in
      let gc = recolour g' o col in
      let fill (g'': heap) : Lemma (fields_written gc g'' x ==> pages_ok_mc g'' st')
        = if FStar.IndefiniteDescription.strong_excluded_middle (fields_written gc g'' x)
          then fill_mc g ys st wz col g''
      in
      FStar.Classical.forall_intro fill
    end

/// **Allocation in any colour that is not blue is correct**, from `pages_ok`
/// up to the colours of live objects.
let alloc_col_correct (col: color) (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok_mc g st /\ col <> Blue)
          (ensures (let (g', st', o) = alloc_col col g st wz in alloc_ok_col col g g' st st' wz o))
  = eliminate exists (ys: list obj_addr). live_list g ys /\ pages_ok (whiten g ys) st
    with alloc_col_ys col g ys st wz

/// **White allocation is the allocator of stage 2**, so `alloc_correct`
/// (`alloc_meets alloc`) is a theorem about `alloc_col White`.
let alloc_col_white (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok_mc g st)
          (ensures alloc_col White g st wz == A.alloc g st wz)
  = eliminate exists (ys: list obj_addr). live_list g ys /\ pages_ok (whiten g ys) st
    with begin
      let (g', st', o) = A.alloc g st wz in
      if o = 0UL then ()
      else begin
        new_facts g ys st wz White;
        let x : obj_addr = o in
        hx_word x;
        colorHeader_same (hdr g' (hx x)) White;
        let aux (b: nat) : Lemma (b < heap_size /\ b % 8 == 0 ==>
                                  read_word (recolour g' o White) (U64.uint_to_t b) == read_word g' (U64.uint_to_t b))
          = if b < heap_size && b % 8 = 0 then wr_read g' (hx x) (hdr g' (hx x)) (U64.uint_to_t b)
        in
        FStar.Classical.forall_intro aux;
        HE.heap_read_word_ext (recolour g' o White) g'
      end
    end

/// `alloc_ok_col White` asks `pages_ok_mc` of the caller's heap where
/// `alloc_ok` asks `pages_ok /\ well_formed_heap`; with `alloc_col_white`,
/// the white allocator still meets the stronger `alloc_ok`.
let alloc_col_white_ok (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok g st /\ well_formed_heap g)
          (ensures (let (g', st', o) = alloc_col White g st wz in alloc_ok g g' st st' wz o))
  = mc_of_ok g st;
    alloc_col_white g st wz;
    A.alloc_ok_at g st wz

/// ---------------------------------------------------------------------------
/// Vacuity
/// ---------------------------------------------------------------------------

/// The precondition holds of the empty heap of pages.
let init_mc (g: heap)
  : Lemma (pages_ok_mc (GC.Spec.Pages.Init.init_heap g) GC.Spec.Pages.Init.init_state)
  = A.init_alloc_pre g;
    mc_of_ok (GC.Spec.Pages.Init.init_heap g) GC.Spec.Pages.Init.init_state

/// On it a black allocation succeeds and gives a black object, so the
/// theorem is not met by always failing.
let init_black (g: heap) (wz: nat)
  : Lemma (requires n_pages > 0 /\ wz + 1 <= small_max)
          (ensures (let (g', st', o) = alloc_col Black (GC.Spec.Pages.Init.init_heap g) GC.Spec.Pages.Init.init_state wz in
                    o =!= 0UL /\ U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                    is_black (o <: obj_addr) g'))
  = let g0 = GC.Spec.Pages.Init.init_heap g in
    let st0 = GC.Spec.Pages.Init.init_state in
    A.init_alloc_succeeds g wz;
    init_mc g;
    alloc_col_correct Black g0 st0 wz;
    let (g', st', o) = alloc_col Black g0 st0 wz in
    is_black_iff (o <: obj_addr) g'

/// After a black allocation the caller can write the fields (clearing them
/// will do), and the heap it gets satisfies the invariant, so the caller's
/// clause is not vacuous.
let init_black_filled (g: heap) (wz: nat)
  : Lemma (requires n_pages > 0 /\ wz + 1 <= small_max)
          (ensures (let (g', st', o) = alloc_col Black (GC.Spec.Pages.Init.init_heap g) GC.Spec.Pages.Init.init_state wz in
                    o =!= 0UL /\ U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                    (let x : obj_addr = o in
                     pages_ok_mc (zeros g' (U64.v x) (U64.v (wosize_of_object x g'))) st')))
  = let g0 = GC.Spec.Pages.Init.init_heap g in
    let st0 = GC.Spec.Pages.Init.init_state in
    init_black g wz;
    init_mc g;
    alloc_col_correct Black g0 st0 wz;
    let (g', st', o) = alloc_col Black g0 st0 wz in
    F.cleared_written g' (o <: obj_addr)

/// The hypotheses of `alloc_col_correct` are not refutable.
#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"
[@@expect_failure [19]]
let alloc_col_hyps_not_false (col: color) (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok_mc g st /\ col <> Blue) (ensures False)
  = ()
#pop-options
