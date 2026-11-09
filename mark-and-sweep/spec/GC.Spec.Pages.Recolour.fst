/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Recolour - the allocator does not read the colours of live objects
/// ---------------------------------------------------------------------------
///
/// An incremental collector allocates while the mark runs, so the heap it
/// hands the allocator has black and grey objects in swept pages, which
/// `pages_ok` (L5, L7) forbids.  This module shows that this does not matter:
/// the allocator reads and writes only words inside free blocks and the
/// allocator state, never the header of an object that is not free.
///
///   - `paint g xs col` is `g` with the headers of the objects `xs`
///     recoloured `col`; `whiten g xs` is `paint g xs White`.
///   - `alloc_paint`: if the objects `ys` are not free and `whiten g ys`
///     satisfies the allocator's precondition, then for `xs` among `ys`,
///     allocating in `g` and in `paint g xs col` gives the same state and
///     object, and heaps that differ only by `paint _ xs col`.
///
/// No header of an object that is not free lies inside a free block
/// (`blue_avoid`, from `GC.Spec.Pages.Fill.apart`), which is all the
/// per-path proofs need.

module GC.Spec.Pages.Recolour

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
open GC.Spec.Pages.Replace

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module HE = GC.Gen.HeapExtensional
module F = GC.Spec.Pages.Fill
module PI = GC.Spec.Pages.PoolInit
module Pool = GC.Spec.Pages.Pool
module LG = GC.Spec.Pages.Large
module NR = GC.Spec.Pages.NewRun
module Cells = GC.Spec.Pages.Cells

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Headers
/// ---------------------------------------------------------------------------

/// The header with `h`'s wosize and tag, and colour `c`.
let hpack (h: U64.t) (c: color) : U64.t =
  get_wosize_bound (U64.v h);
  get_tag_bound (U64.v h);
  pack_header64 { wosize = get_wosize (U64.v h); color = c; tag = get_tag (U64.v h) }

/// A header is its wosize, colour and tag.
let colorHeader_pack (h: U64.t) (c: color)
  : Lemma (colorHeader h c == hpack h c)
  = all_headers_valid h;
    get_wosize_bound (U64.v h);
    get_tag_bound (U64.v h);
    colorHeader_spec h c;
    repack_set_color64 h c

/// Only the last colour counts.
let colorHeader_twice (h: U64.t) (c1 c2: color)
  : Lemma (colorHeader (colorHeader h c1) c2 == colorHeader h c2)
  = let h1 = colorHeader h c1 in
    colorHeader_spec h c1;
    setColor_preserves_wosize (U64.v h) (pack_color c1);
    setColor_preserves_tag (U64.v h) (pack_color c1);
    colorHeader_pack h1 c2;
    colorHeader_pack h c2

/// A header already of colour `c` is kept.
let colorHeader_same (h: U64.t) (c: color)
  : Lemma (requires getColor h == c) (ensures colorHeader h c == h)
  = all_headers_valid h;
    get_wosize_bound (U64.v h);
    get_tag_bound (U64.v h);
    get_color_bound (U64.v h);
    valid_color_unpack (get_color (U64.v h));
    getColor_spec h;
    colorHeader_pack h c;
    unpack_pack_header64 h

/// ---------------------------------------------------------------------------
/// Painting the headers of a list of objects
/// ---------------------------------------------------------------------------

/// The header address of `x`, as a byte offset.
let hx (x: obj_addr) : nat = U64.v x - 8

/// `g` with the headers of `xs` recoloured `col`.
#push-options "--fuel 1"
let rec paint (g: heap) (xs: list obj_addr) (col: color) : GTot heap (decreases xs) =
  match xs with
  | [] -> g
  | x :: xs' -> let g' = paint g xs' col in wr g' (hx x) (colorHeader (hdr g' (hx x)) col)
#pop-options

/// `g` with the headers of `xs` made white.
let whiten (g: heap) (xs: list obj_addr) : GTot heap = paint g xs White

/// `a` is not the header of any of `xs`.
let avoid (xs: list obj_addr) (a: nat) : prop =
  forall (x: obj_addr). L.mem x xs ==> hx x <> a

let avoid_range (xs: list obj_addr) (lo hi: nat) : prop =
  forall (a: nat). lo <= a /\ a < hi ==> avoid xs a

/// Every object of `xs` is one of `ys`.
let sub (xs ys: list obj_addr) : prop = forall (x: obj_addr). L.mem x xs ==> L.mem x ys

let hx_word (x: obj_addr) : Lemma (hx x < heap_size /\ hx x % 8 == 0) = ()

#push-options "--fuel 1"
let rec paint_off (g: heap) (xs: list obj_addr) (col: color) (a: hp_addr)
  : Lemma (requires avoid xs (U64.v a))
          (ensures read_word (paint g xs col) a == read_word g a)
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: xs' ->
      paint_off g xs' col a;
      wr_read (paint g xs' col) (hx x) (colorHeader (hdr (paint g xs' col) (hx x)) col) a

let rec paint_on (g: heap) (xs: list obj_addr) (col: color) (x: obj_addr)
  : Lemma (requires L.mem x xs)
          (ensures hdr (paint g xs col) (hx x) == colorHeader (hdr g (hx x)) col)
          (decreases xs)
  = hx_word x;
    let a = mk_hp_addr (hx x) in
    match xs with
    | y :: xs' ->
      let g' = paint g xs' col in
      wr_read g' (hx y) (colorHeader (hdr g' (hx y)) col) a;
      if hx y = hx x then begin
        if L.mem x xs' then begin
          paint_on g xs' col x;
          colorHeader_twice (hdr g (hx x)) col col
        end else begin
          assert (avoid xs' (hx x));
          paint_off g xs' col a
        end
      end
      else paint_on g xs' col x
#pop-options

/// Every word of `paint g xs col`.
let paint_read (g: heap) (xs: list obj_addr) (col: color) (a: hp_addr)
  : Lemma (read_word (paint g xs col) a ==
           (if FStar.IndefiniteDescription.strong_excluded_middle (avoid xs (U64.v a))
            then read_word g a else colorHeader (read_word g a) col))
  = if FStar.IndefiniteDescription.strong_excluded_middle (avoid xs (U64.v a))
    then paint_off g xs col a
    else begin
      eliminate exists (x: obj_addr). L.mem x xs /\ hx x == U64.v a
      with paint_on g xs col x
    end

/// Painting commutes with a write away from the headers it paints.
let paint_write (g: heap) (xs: list obj_addr) (col: color) (a: hp_addr) (v: U64.t)
  : Lemma (requires avoid xs (U64.v a))
          (ensures paint (write_word g a v) xs col == write_word (paint g xs col) a v)
  = let l = paint (write_word g a v) xs col in
    let r = write_word (paint g xs col) a v in
    let aux (b: nat) : Lemma (b < heap_size /\ b % 8 == 0 ==>
                              read_word l (U64.uint_to_t b) == read_word r (U64.uint_to_t b))
      = if b < heap_size && b % 8 = 0 then begin
          let ba : hp_addr = U64.uint_to_t b in
          paint_read (write_word g a v) xs col ba;
          paint_read g xs col ba;
          if b = U64.v a then begin
            read_write_same g a v;
            read_write_same (paint g xs col) a v
          end else begin
            read_write_different g a ba v;
            read_write_different (paint g xs col) a ba v
          end
        end
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext l r

let paint_wr (g: heap) (xs: list obj_addr) (col: color) (a: nat) (v: U64.t)
  : Lemma (requires avoid xs a)
          (ensures paint (wr g a v) xs col == wr (paint g xs col) a v)
  = if a < heap_size && a % 8 = 0 then paint_write g xs col (mk_hp_addr a) v

let paint_hdr (g: heap) (xs: list obj_addr) (col: color) (a: nat)
  : Lemma (requires avoid xs a) (ensures hdr (paint g xs col) a == hdr g a)
  = if a < heap_size && a % 8 = 0 then paint_off g xs col (mk_hp_addr a)

let whiten_nil (g: heap) : Lemma (whiten g [] == g) = assert_norm (paint g [] White == g)

#push-options "--fuel 2"
let paint_one (g: heap) (y: obj_addr) (c: color)
  : Lemma (paint g [y] c == wr g (hx y) (colorHeader (hdr g (hx y)) c))
  = ()
#pop-options

/// Painting an object its own colour changes nothing.
let paint_own (g: heap) (y: obj_addr)
  : Lemma (paint g [y] (color_at g (hx y)) == g)
  = let c = color_at g (hx y) in
    paint_one g y c;
    colorHeader_same (hdr g (hx y)) c;
    hx_word y;
    let a = mk_hp_addr (hx y) in
    let l = wr g (hx y) (hdr g (hx y)) in
    let aux (b: nat) : Lemma (b < heap_size /\ b % 8 == 0 ==>
                              read_word l (U64.uint_to_t b) == read_word g (U64.uint_to_t b))
      = if b < heap_size && b % 8 = 0 then wr_read g (hx y) (hdr g (hx y)) (U64.uint_to_t b)
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext l g

/// ---------------------------------------------------------------------------
/// No painted header lies inside a free block
/// ---------------------------------------------------------------------------

/// The objects `xs` are objects of `gw` that are not free there.
let live_in (gw: heap) (xs: list obj_addr) : prop =
  forall (x: obj_addr). L.mem x xs ==>
    Seq.mem x (objects zero_addr gw) /\ color_at gw (hx x) =!= Blue

/// A free block the walk reaches holds no header of `xs`.
let blue_avoid (gw: heap) (xs: list obj_addr) (p: nat)
  : Lemma (requires live_in gw xs /\ steps_to gw z p /\ color_at gw p == Blue)
          (ensures avoid_range xs p (p + words_at gw p * 8))
  = let one (x: obj_addr) : Lemma (L.mem x xs ==> ~(p <= hx x /\ hx x < p + words_at gw p * 8))
      = if L.mem x xs && hx x <> p then F.apart gw x p
    in
    FStar.Classical.forall_intro one

/// ---------------------------------------------------------------------------
/// Whitening keeps the walk
/// ---------------------------------------------------------------------------

let whiten_step_eq (g: heap) (x: obj_addr)
  : Lemma (wr g (hx x) (colorHeader (hdr g (hx x)) White) == set_object_color x g White)
  = hd_address_spec x;
    makeWhite_spec x g;
    makeWhite_eq x g;
    assert (mk_hp_addr (hx x) == hd_address x)

#push-options "--fuel 1"
let rec whiten_objects (g: heap) (xs: list obj_addr)
  : Lemma (ensures objects zero_addr (whiten g xs) == objects zero_addr g) (decreases xs)
  = match xs with
    | [] -> ()
    | x :: xs' ->
      whiten_objects g xs';
      whiten_step_eq (whiten g xs') x;
      color_change_preserves_objects (whiten g xs') x White
#pop-options

/// The objects of `xs`, in `g`, are white objects of `whiten g xs`.
let whiten_wh (g: heap) (xs: list obj_addr)
  : Lemma (requires forall (x: obj_addr). L.mem x xs ==> Seq.mem x (objects zero_addr g))
          (ensures live_in (whiten g xs) xs /\
                   (forall (x: obj_addr). L.mem x xs ==> color_at (whiten g xs) (hx x) == White))
  = whiten_objects g xs;
    let one (x: obj_addr) : Lemma (L.mem x xs ==> color_at (whiten g xs) (hx x) == White)
      = if L.mem x xs then begin
          paint_on g xs White x;
          colorHeader_getColor (hdr g (hx x)) White
        end
    in
    FStar.Classical.forall_intro one

/// ---------------------------------------------------------------------------
/// The context of every commutation lemma
/// ---------------------------------------------------------------------------

/// `whiten g ys` satisfies the allocator's precondition, the objects `ys`
/// are not free in it, and the painted objects `xs` are among them.
let ctx (g: heap) (ys xs: list obj_addr) (st: pstate) : prop =
  live_in (whiten g ys) ys /\ pages_ok (whiten g ys) st /\ well_formed_heap (whiten g ys) /\
  sub xs ys

let avoid_sub (xs ys: list obj_addr) (lo hi: nat)
  : Lemma (requires avoid_range ys lo hi /\ sub xs ys) (ensures avoid_range xs lo hi)
  = ()

/// ---------------------------------------------------------------------------
/// The pool path
/// ---------------------------------------------------------------------------

/// The slot `pop` takes, if it takes one.
let pop_at (st: pstate) (c: nat{c < n_cls}) : option (nat & nat) =
  let hd = Pool.avail_at st c in
  if hd = 0UL || U64.v hd - 1 >= n_pages then None
  else begin
    let p : nat = U64.v hd - 1 in
    let e = entry st.pm p in
    let k = Pool.slot_of p c e.free_head in
    if k >= n_slots c || e.nfree = 0 then None else Some (p, k)
  end

/// The slot `pop` takes is a free block the walk reaches.
let pop_slot (gw: heap) (st: pstate) (c: nat{c < n_cls})
  : Lemma (requires pages_ok gw st /\ well_formed_heap gw /\ Some? (pop_at st c))
          (ensures (let Some (p, k) = pop_at st c in
                    p < n_pages /\ k < n_slots c /\ slot_free gw p c k /\
                    steps_to gw z (slot_base p c k)))
  = let Some (p, k) = pop_at st c in
    Pool.pop_ctx_intro gw st c;
    eliminate exists (k': nat) (ks ps: list nat). Pool.pop_ctx gw st c p k' ks ps
    with begin
      Pool.slot_of_obj p c k' (entry st.pm p).free_head;
      GC.Spec.Pages.Step.pages_ok_elim gw st;
      assert (page_shape gw st.pm p);
      walk_pages_reached gw st.pm p;
      slots_steps gw p c k;
      steps_to_trans gw z (page_base p) (slot_base p c k)
    end

let fill_paint (g: heap) (xs: list obj_addr) (col: color)
               (p: nat{p < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
               (wz: nat{Pool.small_wz wz c})
  : Lemma (requires avoid_range xs (slot_base p c k) (slot_base p c k + cls c * 8))
          (ensures paint (Pool.fill_slot_as false g p c k wz) xs col ==
                   Pool.fill_slot_as false (paint g xs col) p c k wz)
  = cls_bounds c;
    FStar.Math.Lemmas.pow2_lt_compat 54 20;
    let a = slot_base p c k in
    if wz + 1 < cls c then begin
      let f = a + (wz + 1) * 8 in
      let v = bhdr (cls c - (wz + 1)) in
      paint_wr g xs col f v;
      paint_wr (wr g f v) xs col a (ohdr wz)
    end
    else paint_wr g xs col a (ohdr wz)

let pop_paint (g: heap) (ys xs: list obj_addr) (col: color) (st: pstate) (c: nat{c < n_cls})
              (wz: nat{Pool.small_wz wz c})
  : Lemma (requires ctx g ys xs st)
          (ensures (let (g', st', o) = Pool.pop_as false g st c wz in
                    Pool.pop_as false (paint g xs col) st c wz == (paint g' xs col, st', o)))
  = let gw = whiten g ys in
    match pop_at st c with
    | None -> ()
    | Some (p, k) ->
      pop_slot gw st c;
      cls_bounds c;
      blue_avoid gw ys (slot_base p c k);
      avoid_sub xs ys (slot_base p c k) (slot_base p c k + cls c * 8);
      paint_hdr g xs col (slot_obj p c k);
      fill_paint g xs col p c k wz

/// ---------------------------------------------------------------------------
/// Taking a free page
/// ---------------------------------------------------------------------------

/// A free page is one free block the walk reaches.
let free_page_avoid (gw: heap) (st: pstate) (xs: list obj_addr) (i: nat{i < n_pages})
  : Lemma (requires live_in gw xs /\ pages_ok gw st /\ (entry st.pm i).kind == Free)
          (ensures avoid_range xs (page_base i) (page_base (i + 1)))
  = GC.Spec.Pages.Step.pages_ok_elim gw st;
    assert (page_shape gw st.pm i);
    walk_pages_reached gw st.pm i;
    blue_avoid gw xs (page_base i)

#push-options "--fuel 1"
let rec write_slots_paint (g: heap) (xs: list obj_addr) (col: color)
                          (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k <= n_slots c})
  : Lemma (requires avoid_range xs (page_base i) (page_base (i + 1)))
          (ensures paint (PI.write_slots g i c k) xs col == PI.write_slots (paint g xs col) i c k)
          (decreases k)
  = if k = 0 then ()
    else begin
      write_slots_paint g xs col i c (k - 1);
      PI.slot_fits i c (k - 1);
      let g1 = PI.write_slots g i c (k - 1) in
      paint_write g1 xs col (PI.slot_hd i c (k - 1)) (PI.slot_hdr c);
      paint_write (write_word g1 (PI.slot_hd i c (k - 1)) (PI.slot_hdr c)) xs col
                  (PI.slot_link i c (k - 1)) (PI.link_val i c (k - 1))
    end
#pop-options

let pool_init_paint (g: heap) (xs: list obj_addr) (col: color) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires avoid_range xs (page_base i) (page_base (i + 1)))
          (ensures paint (PI.pool_init g i c) xs col == PI.pool_init (paint g xs col) i c)
  = write_slots_paint g xs col i c (n_slots c);
    if tail_words c > 0 then begin
      slots_fill_page i c;
      page_base_mono (i + 1) n_pages;
      slot_base_aligned i c (n_slots c);
      cls_bounds c;
      paint_write (PI.write_slots g i c (n_slots c)) xs col (mk_hp_addr (slots_end i c)) (PI.tail_filler_hdr c)
    end

/// Objects that are not free stay so across a step that keeps them.
let live_in_step (gw gw1: heap) (xs: list obj_addr)
  : Lemma (requires live_in gw xs /\ GC.Spec.Pages.Theorems.others_unchanged gw gw1)
          (ensures live_in gw1 xs)
  = let one (x: obj_addr) : Lemma (L.mem x xs ==> Seq.mem x (objects zero_addr gw1) /\ color_at gw1 (hx x) =!= Blue)
      = if L.mem x xs then begin
          hdr_obj gw x;
          hdr_obj gw1 x;
          is_blue_iff x gw
        end
    in
    FStar.Classical.forall_intro one

/// ---------------------------------------------------------------------------
/// Small blocks
/// ---------------------------------------------------------------------------

let small_paint (g: heap) (ys xs: list obj_addr) (col: color) (st: pstate) (wz: nat{wz + 1 <= small_max})
  : Lemma (requires ctx g ys xs st)
          (ensures (let (g', st', o) = Pool.small_alloc_as false g st wz in
                    Pool.small_alloc_as false (paint g xs col) st wz == (paint g' xs col, st', o)))
  = let gw = whiten g ys in
    let c = class_of (wz + 1) in
    class_of_fits (wz + 1);
    Pool.small_wz_intro wz c;
    if Pool.avail_at st c <> 0UL then pop_paint g ys xs col st c wz
    else begin
      let i = Pool.find_free st.pm 0 in
      Pool.find_free_spec st.pm 0;
      if i >= n_pages then ()
      else begin
        free_page_avoid gw st ys i;
        avoid_sub xs ys (page_base i) (page_base (i + 1));
        pool_init_paint g xs col i c;
        pool_init_paint g ys White i c;
        Pool.acquire_ok gw st i c;
        let g1 = PI.pool_init g i c in
        let st1 = Pool.acq_state st i c in
        live_in_step gw (whiten g1 ys) ys;
        pop_paint g1 ys xs col st1 c wz
      end
    end

/// ---------------------------------------------------------------------------
/// The large list
/// ---------------------------------------------------------------------------

let whsize_paint (g: heap) (xs: list obj_addr) (col: color) (c: obj_addr)
  : Lemma (requires avoid xs (hx c)) (ensures whsize (paint g xs col) c == whsize g c)
  = hd_address_spec c;
    hx_word c;
    paint_off g xs col (hd_address c);
    wosize_of_object_spec c g;
    wosize_of_object_spec c (paint g xs col)

/// A cell of list 0 is a free block the walk reaches, with a field.
let cell_avoid (gw: heap) (st: pstate) (xs: list obj_addr) (y: obj_addr)
  : Lemma (requires live_in gw xs /\ pages_ok gw st /\
                    L.mem y (Cells.walk gw (Cells.large_head st) heap_words))
          (ensures avoid_range xs (hx y) (hx y + whsize gw y * 8) /\ whsize gw y >= 2 /\
                   avoid xs (hx y) /\ avoid xs (U64.v y))
  = GC.Spec.Pages.Step.pages_ok_elim gw st;
    Cells.large_ok_lview gw st;
    let cs = Cells.walk gw (Cells.large_head st) heap_words in
    Cells.cells_mem gw (Cells.large_head st) cs y;
    hdr_obj gw y;
    obj_iff gw y;
    is_blue_iff y gw;
    blue_avoid gw xs (hx y)

#push-options "--fuel 1"
/// Two heaps that agree on the links of the cells walk the same list.
let rec walk_agree (h1 h2: heap) (fp: U64.t) (n: nat)
  : Lemma (requires forall (y: obj_addr). L.mem y (Cells.walk h2 fp n) ==>
                      read_word h1 (y <: hp_addr) == read_word h2 (y <: hp_addr))
          (ensures Cells.walk h1 fp n == Cells.walk h2 fp n)
          (decreases n)
  = if n = 0 || not (Cells.node fp) then ()
    else begin
      let y : obj_addr = fp in
      walk_agree h1 h2 (read_word h1 (y <: hp_addr)) (n - 1)
    end

let rec split_fit_agree (h1 h2: heap) (cs: list obj_addr) (w: nat)
  : Lemma (requires forall (y: obj_addr). L.mem y cs ==> whsize h1 y == whsize h2 y)
          (ensures LG.split_fit h1 cs w == LG.split_fit h2 cs w)
          (decreases cs)
  = match cs with
    | [] -> ()
    | c :: rest -> split_fit_agree h1 h2 rest w

let rec last_mem (l: list obj_addr{Cons? l})
  : Lemma (ensures L.mem (L.last l) l) (decreases l)
  = match l with
    | [_] -> ()
    | _ :: tl -> last_mem tl
#pop-options

let carved_paint (g: heap) (xs: list obj_addr) (col: color) (c: obj_addr) (wz: nat{wz < pow2 54})
  : Lemma (requires avoid_range xs (hx c) (hx c + whsize g c * 8) /\ wz + 1 <= whsize g c)
          (ensures LG.rem_of (paint g xs col) c wz == LG.rem_of g c wz /\
                   LG.obj_of (paint g xs col) c wz == LG.obj_of g c wz /\
                   paint (LG.carved_as false g c wz) xs col == LG.carved_as false (paint g xs col) c wz)
  = whsize_paint g xs col c;
    let h = LG.hd_of c in
    let l = LG.rem_of g c wz in
    if l >= 1 && l <= pow2 54 then begin
      paint_wr g xs col h (bhdr l);
      paint_wr (put_blue g h l) xs col (h + l * 8) (ohdr wz)
    end
    else paint_wr g xs col h (ohdr wz)

let carve_paint (g: heap) (xs: list obj_addr) (col: color) (st: pstate) (pre: list obj_addr) (c: obj_addr)
                (wz: nat{wz < pow2 54})
  : Lemma (requires avoid_range xs (hx c) (hx c + whsize g c * 8) /\ whsize g c >= 2 /\
                    (forall (y: obj_addr). L.mem y pre ==> avoid xs (U64.v y) /\ U64.v y <> hx c))
          (ensures (let (g', st', o) = LG.carve_as false g st pre c wz in
                    LG.carve_as false (paint g xs col) st pre c wz == (paint g' xs col, st', o)))
  = whsize_paint g xs col c;
    if whsize g c < wz + 1 then ()
    else if LG.rem_of g c wz >= lg_min then carved_paint g xs col c wz
    else begin
      hx_word c;
      paint_off g xs col (c <: hp_addr);
      let nx = read_word g (c <: hp_addr) in
      let g1 = LG.unlink_heap g st pre nx in
      (match pre with
       | [] -> ()
       | _ -> last_mem pre; paint_wr g xs col (U64.v (L.last pre)) nx);
      assert (paint g1 xs col == LG.unlink_heap (paint g xs col) st pre nx);
      whsize_paint g1 xs col c;
      if Cons? pre then begin
        last_mem pre;
        hd_address_spec c;
        wosize_of_object_spec c g;
        wosize_of_object_spec c g1;
        wr_read g (U64.v (L.last pre)) nx (hd_address c)
      end;
      carved_paint g1 xs col c wz
    end

/// ---------------------------------------------------------------------------
/// A new run
/// ---------------------------------------------------------------------------

let page_base_add (i k: nat) : Lemma (page_base (i + k) == page_base i + k * page_wsize * 8)
  = FStar.Math.Lemmas.distributivity_add_left i k page_bytes;
    FStar.Math.Lemmas.paren_mul_right k page_wsize 8

#push-options "--fuel 1"
let rec free_pages_avoid (gw: heap) (st: pstate) (xs: list obj_addr) (i k: nat)
  : Lemma (requires live_in gw xs /\ pages_ok gw st /\ GC.Spec.Pages.Theorems.free_run st.pm i k)
          (ensures avoid_range xs (page_base i) (page_base (i + k)))
          (decreases k)
  = if k = 0 then ()
    else begin
      free_pages_avoid gw st xs i (k - 1);
      free_page_avoid gw st xs (i + k - 1)
    end
#pop-options

let run_heap_paint (g: heap) (xs: list obj_addr) (col: color)
                   (i: nat) (k: pos) (wz: nat{wz < pow2 54}) (hd0: U64.t)
  : Lemma (requires avoid_range xs (page_base i) (page_base (i + k)) /\ wz + 1 <= k * page_wsize)
          (ensures paint (NR.run_heap_as false g i k wz hd0) xs col ==
                   NR.run_heap_as false (paint g xs col) i k wz hd0)
  = let a = page_base i in
    let w = wz + 1 in
    let r = NR.rest k w in
    page_base_add i k;
    let g1 =
      if r > 0 && r <= pow2 54 then begin
        let g2 = put_blue g (a + w * 8) r in
        paint_wr g xs col (a + w * 8) (bhdr r);
        if r >= lg_min then begin
          paint_wr g2 xs col (a + w * 8 + 8) hd0;
          wr g2 (a + w * 8 + 8) hd0
        end
        else g2
      end
      else g
    in
    paint_wr g1 xs col a (ohdr wz)

/// ---------------------------------------------------------------------------
/// Large blocks
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec not_in_pre (pre: list obj_addr) (c: obj_addr) (post: list obj_addr)
  : Lemma (requires L.noRepeats (L.append pre (c :: post))) (ensures ~(L.mem c pre)) (decreases pre)
  = match pre with
    | [] -> ()
    | y :: pre' ->
      FStar.List.Tot.Properties.append_mem pre' (c :: post) y;
      not_in_pre pre' c post
#pop-options

/// The link word of another cell is not the header of `c`.
let link_not_hdr (gw: heap) (y c: obj_addr)
  : Lemma (requires Seq.mem y (objects zero_addr gw) /\ Seq.mem c (objects zero_addr gw) /\
                    y <> c /\ U64.v (wosize_of_object y gw) >= 1)
          (ensures U64.v y <> hx c)
  = obj_iff gw c;
    F.apart gw y (hx c)

/// The list the large path walks is the same in `g`, `paint g xs col` and
/// `whiten g ys`.
let walks_same (g: heap) (ys xs: list obj_addr) (col: color) (st: pstate)
  : Lemma (requires ctx g ys xs st)
          (ensures (let h = Cells.large_head st in
                    let cs = Cells.walk (whiten g ys) h heap_words in
                    Cells.walk g h heap_words == cs /\ Cells.walk (paint g xs col) h heap_words == cs /\
                    (forall (y: obj_addr). L.mem y cs ==>
                       whsize g y == whsize (whiten g ys) y /\ whsize (paint g xs col) y == whsize g y)))
  = let gw = whiten g ys in
    let h = Cells.large_head st in
    let cs = Cells.walk gw h heap_words in
    let one (y: obj_addr)
      : Lemma (L.mem y cs ==>
                 read_word g (y <: hp_addr) == read_word gw (y <: hp_addr) /\
                 read_word (paint g xs col) (y <: hp_addr) == read_word gw (y <: hp_addr) /\
                 whsize g y == whsize gw y /\ whsize (paint g xs col) y == whsize g y)
      = if L.mem y cs then begin
          cell_avoid gw st ys y;
          paint_off g ys White (y <: hp_addr);
          paint_off g xs col (y <: hp_addr);
          whsize_paint g ys White y;
          whsize_paint g xs col y
        end
    in
    FStar.Classical.forall_intro one;
    walk_agree g gw h heap_words;
    walk_agree (paint g xs col) gw h heap_words

let large_paint (g: heap) (ys xs: list obj_addr) (col: color) (st: pstate) (wz: nat{wz < pow2 54})
  : Lemma (requires ctx g ys xs st)
          (ensures (let (g', st', o) = GC.Spec.Pages.Alloc.large_alloc_as false g st wz in
                    GC.Spec.Pages.Alloc.large_alloc_as false (paint g xs col) st wz == (paint g' xs col, st', o)))
  = let gw = whiten g ys in
    let h = Cells.large_head st in
    let cs = Cells.walk gw h heap_words in
    walks_same g ys xs col st;
    split_fit_agree g gw cs (wz + 1);
    split_fit_agree (paint g xs col) g cs (wz + 1);
    match LG.split_fit gw cs (wz + 1) with
    | Some (pre, c, post) ->
      LG.split_fit_some gw cs (wz + 1) pre c post;
      FStar.List.Tot.Properties.append_mem_forall pre (c :: post);
      LG.mem_cons_obj c c post;
      GC.Spec.Pages.Step.pages_ok_elim gw st;
      Cells.large_ok_lview gw st;
      not_in_pre pre c post;
      Cells.cells_mem gw h cs c;
      cell_avoid gw st ys c;
      avoid_sub xs ys (hx c) (hx c + whsize gw c * 8);
      let one (y: obj_addr) : Lemma (L.mem y pre ==> avoid xs (U64.v y) /\ U64.v y <> hx c)
        = if L.mem y pre then begin
            Cells.cells_mem gw h cs y;
            cell_avoid gw st ys y;
            link_not_hdr gw y c
          end
      in
      FStar.Classical.forall_intro one;
      carve_paint g xs col st pre c wz
    | None ->
      let k = GC.Spec.Pages.Theorems.pages_for (wz + 1) in
      let i = NR.find_run st.pm k 0 in
      NR.find_run_spec st.pm k 0;
      if i + k > n_pages then ()
      else begin
        free_pages_avoid gw st ys i k;
        avoid_sub xs ys (page_base i) (page_base (i + k));
        NR.pages_for_spec (wz + 1);
        run_heap_paint g xs col i k wz h
      end

/// ---------------------------------------------------------------------------
/// The allocator
/// ---------------------------------------------------------------------------

/// **The allocator does not see the colours of the objects `ys`.**  If
/// `whiten g ys` meets its precondition, then for any `xs` among `ys` and
/// any colour, allocating in `g` and in `g` with `xs` repainted gives the
/// same state and object, and the same heap up to that repainting.
let alloc_paint (g: heap) (ys xs: list obj_addr) (col: color) (st: pstate) (wz: nat)
  : Lemma (requires ctx g ys xs st)
          (ensures (let (g', st', o) = GC.Spec.Pages.Alloc.alloc g st wz in
                    GC.Spec.Pages.Alloc.alloc (paint g xs col) st wz == (paint g' xs col, st', o)))
  = if wz + 1 >= pow2 54 then ()
    else if wz + 1 <= small_max then small_paint g ys xs col st wz
    else large_paint g ys xs col st wz
