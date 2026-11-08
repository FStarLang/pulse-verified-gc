/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Large - allocating from the large list
/// ---------------------------------------------------------------------------
///
/// A large block of `w = wz + 1` words, header included, is taken from #46's
/// first-fit list 0, restricted to swept runs (L9):
///   - `split_fit` finds the first listed block of at least `w` words;
///   - the object is carved from the block's right end, as #46 does, and its
///     fields are cleared;
///   - a remainder of at least `lg_min` words stays where it is, on the list,
///     as a smaller block;
///   - a smaller remainder, or none, leaves the list: the block is unlinked,
///     by rewriting the link of the block before it, or the list head, and
///     the remainder stays as an unlisted free piece.
///
/// `carve_ok` proves `alloc_ok` of the result.  Run growth, used when no
/// listed block fits, is `GC.Spec.Pages.NewRun`.

module GC.Spec.Pages.Large

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
open GC.Spec.Pages.Run
open GC.Spec.Pages.Theorems

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module Mark = GC.Spec.Mark
module FLs = GC.Spec.FreeLists

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The specification
/// ---------------------------------------------------------------------------

/// The cells before the first one of at least `w` words, that cell, and the
/// cells after it.
#push-options "--fuel 1"
let rec split_fit (g: heap) (cs: list obj_addr) (w: nat)
  : GTot (option (list obj_addr & obj_addr & list obj_addr)) (decreases cs)
  = match cs with
    | [] -> None
    | c :: rest ->
      if whsize g c >= w then Some ([], c, rest)
      else (match split_fit g rest w with
            | None -> None
            | Some (pre, d, post) -> Some (c :: pre, d, post))
#pop-options

/// A free block of `l` words at `h`, then an object of wosize `wz`; or only
/// the object, when `l = 0`.
let carve_heap (g: heap) (h: nat) (l: nat) (wz: nat{wz < pow2 54}) : GTot heap =
  if l >= 1 && l <= pow2 54 then put_obj (put_blue g h l) (h + l * 8) wz
  else put_obj g h wz

let obj_at (x: nat) : U64.t = if x < pow2 64 then U64.uint_to_t x else 0UL

let obj_at_spec (x: nat)
  : Lemma (requires x < heap_size) (ensures U64.v (obj_at x) == x)
  = ()

/// Take a block off list 0, the cells before it being `pre`: rewrite the link
/// of the last of them, or the head.
let unlink (g: heap) (st: pstate) (pre: list obj_addr) (nx: U64.t) : GTot (heap & pstate) =
  match pre with
  | [] -> (g, { st with large = FLs.fls_set st.large 0 nx })
  | _ -> (wr g (U64.v (L.last pre)) nx, st)

let unlink_heap (g: heap) (st: pstate) (pre: list obj_addr) (nx: U64.t) : GTot heap =
  fst (unlink g st pre nx)

let unlink_state (g: heap) (st: pstate) (pre: list obj_addr) (nx: U64.t) : GTot pstate =
  snd (unlink g st pre nx)

let hd_of (c: obj_addr) : nat = U64.v c - 8

/// The words left of cell `c` after carving `wz + 1` words.
let rem_of (g: heap) (c: obj_addr) (wz: nat) : GTot nat =
  if whsize g c >= wz + 1 then whsize g c - (wz + 1) else 0

let obj_of (g: heap) (c: obj_addr) (wz: nat) : GTot U64.t = obj_at (hd_of c + rem_of g c wz * 8 + 8)

let carved (g: heap) (c: obj_addr) (wz: nat{wz < pow2 54}) : GTot heap =
  carve_heap g (hd_of c) (rem_of g c wz) wz

/// Carve an object of wosize `wz` from the right end of cell `c`.
let carve (g: heap) (st: pstate) (pre: list obj_addr) (c: obj_addr) (wz: nat{wz < pow2 54})
  : GTot (heap & pstate & U64.t)
  = if whsize g c < wz + 1 then (g, st, 0UL)
    else if rem_of g c wz >= lg_min then (carved g c wz, st, obj_of g c wz)
    else begin
      let nx = read_word g (c <: hp_addr) in
      let g1 = unlink_heap g st pre nx in
      (carved g1 c wz, unlink_state g st pre nx, obj_of g1 c wz)
    end

/// ---------------------------------------------------------------------------
/// First fit
/// ---------------------------------------------------------------------------

#push-options "--fuel 2"
let rec split_fit_some (g: heap) (cs: list obj_addr) (w: nat)
                       (pre: list obj_addr) (c: obj_addr) (post: list obj_addr)
  : Lemma (requires split_fit g cs w == Some (pre, c, post))
          (ensures cs == pre @ (c :: post) /\ whsize g c >= w /\
                   (forall (y: obj_addr). L.mem y pre ==> whsize g y < w))
          (decreases cs)
  = match cs with
    | c0 :: rest ->
      if whsize g c0 >= w then ()
      else (match split_fit g rest w with
            | Some (pre', d, post') -> split_fit_some g rest w pre' d post')

let rec split_fit_none (g: heap) (cs: list obj_addr) (w: nat)
  : Lemma (requires None? (split_fit g cs w))
          (ensures forall (y: obj_addr). L.mem y cs ==> whsize g y < w)
          (decreases cs)
  = match cs with
    | [] -> ()
    | c :: rest -> split_fit_none g rest w
#pop-options

/// ---------------------------------------------------------------------------
/// The carved block
/// ---------------------------------------------------------------------------

let carve_read (g: heap) (h: nat) (l: nat) (wz: nat{wz < pow2 54}) (x: hp_addr)
  : Lemma (requires h % 8 == 0 /\ l <= pow2 54)
          (ensures read_word (carve_heap g h l wz) x ==
                   (if U64.v x = h + l * 8 then ohdr wz
                    else if h + l * 8 < U64.v x && U64.v x < h + (l + wz + 1) * 8 then 0UL
                    else if l >= 1 && U64.v x = h then bhdr l
                    else read_word g x))
  = aligned_plus_mul8 h l;
    if l >= 1 then begin
      put_obj_read (put_blue g h l) (h + l * 8) wz x;
      wr_read g h (bhdr l) x
    end
    else put_obj_read g h wz x;
    FStar.Math.Lemmas.distributivity_add_left l (wz + 1) 8

/// The carved block, read back.
let carve_basic (g: heap) (h: nat) (l: nat) (wz: nat{wz < pow2 54})
  : Lemma (requires h % 8 == 0 /\ h + (l + wz + 1) * 8 <= heap_size /\ l <= pow2 54)
          (ensures (let g' = carve_heap g h l wz in
                    let e = h + (l + wz + 1) * 8 in
                    let o = h + l * 8 in
                    o % 8 == 0 /\ o + (wz + 1) * 8 == e /\
                    (forall (x: hp_addr). U64.v x < h \/ U64.v x >= e ==> read_word g' x == read_word g x) /\
                    words_at g' o == wz + 1 /\ color_at g' o == White /\ new_block_ok g' o /\
                    (l >= 1 ==> words_at g' h == l /\ color_at g' h == Blue /\ new_block_ok g' h) /\
                    (l >= 2 ==> read_word g' (mk_hp_addr (h + 8)) == read_word g (mk_hp_addr (h + 8)))))
  = let g' = carve_heap g h l wz in
    let o = h + l * 8 in
    FStar.Math.Lemmas.distributivity_add_left l (wz + 1) 8;
    aligned_plus_mul8 h l;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (carve_read g h l wz));
    carve_read g h l wz (mk_hp_addr o);
    obj_block g' o wz;
    if l >= 1 then begin
      carve_read g h l wz (mk_hp_addr h);
      blue_block_ok g' h l;
      if l >= 2 then carve_read g h l wz (mk_hp_addr (h + 8))
    end

/// The walk reaches the object.
let carve_steps_o (g: heap) (h: nat) (l: nat) (wz: nat{wz < pow2 54})
  : Lemma (requires h % 8 == 0 /\ h + (l + wz + 1) * 8 <= heap_size /\ l <= pow2 54)
          (ensures steps_to (carve_heap g h l wz) h (h + l * 8))
  = carve_basic g h l wz;
    if l >= 1 then block_steps (carve_heap g h l wz) h l
    else steps_to_refl (carve_heap g h l wz) h

/// The walk over the carved block.
let carve_walk (g: heap) (h: nat) (l: nat) (wz: nat{wz < pow2 54})
  : Lemma (requires h % 8 == 0 /\ h + (l + wz + 1) * 8 <= heap_size /\ l <= pow2 54)
          (ensures (let g' = carve_heap g h l wz in
                    let e = h + (l + wz + 1) * 8 in
                    let o = h + l * 8 in
                    steps_to g' h e /\ steps_to g' h o /\
                    (forall (b: nat). steps_to g' h b /\ b < e ==>
                       new_block_ok g' b /\ (b == o \/ (l >= 1 /\ b == h))) /\
                    layout_ok g' h e))
  = let g' = carve_heap g h l wz in
    carve_basic g h l wz;
    if l >= 1 then begin
      two_blocks g' h l (wz + 1);
      block_steps g' h l
    end
    else begin
      two_blocks g' h (wz + 1) 0;
      steps_to_refl g' h
    end

/// The stretch of the carved block: a free block of `l` words, if any, then
/// the object.
let carve_layout (g: heap) (h: nat) (l: nat) (wz: nat{wz < pow2 54})
  : Lemma (requires h % 8 == 0 /\ h + (l + wz + 1) * 8 <= heap_size /\ l <= pow2 54)
          (ensures (let g' = carve_heap g h l wz in
                    let e = h + (l + wz + 1) * 8 in
                    let o = h + l * 8 in
                    (forall (x: hp_addr). U64.v x < h \/ U64.v x >= e ==> read_word g' x == read_word g x) /\
                    words_at g' o == wz + 1 /\ color_at g' o == White /\
                    (l >= 1 ==> words_at g' h == l /\ color_at g' h == Blue) /\
                    (l >= 2 ==> read_word g' (mk_hp_addr (h + 8)) == read_word g (mk_hp_addr (h + 8))) /\
                    steps_to g' h e /\ steps_to g' h o /\
                    (forall (b: nat). steps_to g' h b /\ b < e ==>
                       new_block_ok g' b /\ (b == o \/ (l >= 1 /\ b == h))) /\
                    layout_ok g' h e))
  = carve_basic g h l wz;
    carve_walk g h l wz

/// ---------------------------------------------------------------------------
/// A rewrite inside a swept run
/// ---------------------------------------------------------------------------

let page_local_all (g: heap) (pm: page_map) : prop =
  forall (i: nat{i < n_pages}). page_local g pm i

let cont_local (g: heap) (pm: page_map) (j: nat{j < n_pages})
  : Lemma (requires (entry pm j).kind == LargeCont) (ensures page_local g pm j)
  = ()

let combine_run_pages (g: heap) (pm: page_map) (hh: nat{hh < n_pages})
  : Lemma (requires map_ok pm /\ LargeHead? (entry pm hh).kind /\ page_local g pm hh /\
                    (forall (j: nat{j < n_pages}). j < hh \/ j >= hh + run_len (entry pm hh).kind ==>
                       page_local g pm j))
          (ensures page_local_all g pm)
  = assert (run_ok pm hh);
    let n = run_len (entry pm hh).kind in
    let all (j: nat{j < n_pages}) : Lemma (page_local g pm j)
      = if j > hh && j < hh + n then cont_local g pm j
    in
    FStar.Classical.forall_intro all

let unswept_run (g g': heap) (st: pstate) (hh: nat{hh < n_pages})
  : Lemma (requires map_ok st.pm /\ LargeHead? (entry st.pm hh).kind /\ (entry st.pm hh).swept == true /\
                    (forall (x: hp_addr). U64.v x < page_base hh \/
                       U64.v x >= page_base (hh + run_len (entry st.pm hh).kind) ==>
                       read_word g' x == read_word g x))
          (ensures unswept_unchanged g g' st st)
  = let pm = st.pm in
    let n = run_len (entry pm hh).kind in
    assert (run_ok pm hh);
    let unswept (j: nat{j < n_pages})
      : Lemma (not (entry pm j).swept ==> page_kept g g' j)
      = if not (entry pm j).swept then begin
          if j < hh then page_base_mono (j + 1) hh
          else if j >= hh + n then page_base_mono (hh + n) j
        end
    in
    FStar.Classical.forall_intro unswept

/// **Rewriting one free block of a swept run keeps every page-local clause,
/// well-formedness, and every page outside the run.**
let run_region_step (g g': heap) (st: pstate) (hh: nat{hh < n_pages}) (a e: nat)
  : Lemma (requires map_ok st.pm /\ page_local_all g st.pm /\ tail_shape g /\
                    run_ctx g g' st.pm hh a e /\ well_formed_heap g /\ Mark.no_pointer_to_blue g)
          (ensures page_local_all g' st.pm /\ tail_shape g' /\ well_formed_heap g' /\
                   Mark.no_pointer_to_blue g' /\ others_unchanged g g' /\
                   unswept_unchanged g g' st st)
  = let pm = st.pm in
    let n = run_len (entry pm hh).kind in
    assert (run_ok pm hh);
    replace_ok g g' a e;
    run_after_replace g g' pm hh a e;
    page_base_mono hh (hh + n);
    page_base_mono (hh + n) n_pages;
    assert (forall (x: hp_addr). U64.v x < page_base hh \/ U64.v x >= page_base (hh + n) ==>
              read_word g' x == read_word g x);
    others_local g g' pm pm hh (hh + n);
    combine_run_pages g' pm hh;
    tail_kept g g' (hh + n);
    unswept_run g g' st hh

/// A listed cell is a free block of a swept run, wholly inside it.
let cell_in_run (g: heap) (st: pstate) (y: obj_addr) (hh: nat{hh < n_pages})
  : Lemma (requires pages_ok g st /\ Seq.mem y (objects zero_addr g) /\ is_blue y g /\
                    LargeHead? (entry st.pm hh).kind /\ (entry st.pm hh).swept == true /\
                    page_base hh <= U64.v y - 8 /\
                    U64.v y - 8 < page_base (hh + run_len (entry st.pm hh).kind))
          (ensures (let n = run_len (entry st.pm hh).kind in
                    let a = U64.v y - 8 in
                    run_shape g hh n /\ run_swept_ok g st.pm hh /\
                    steps_to g z a /\ steps_to g (page_base hh) a /\
                    a + words_at g a * 8 <= page_base (hh + n) /\
                    color_at g a == Blue /\ a % 8 == 0 /\
                    words_at g a == whsize g y))
  = let n = run_len (entry st.pm hh).kind in
    let a = U64.v y - 8 in
    pages_ok_elim g st;
    assert (page_local g st.pm hh);
    assert (walk_page st.pm hh);
    walk_pages_reached g st.pm hh;
    obj_iff g y;
    hdr_obj g y;
    is_blue_iff y g;
    steps_to_det g z (page_base hh) a;
    block_before g (page_base hh) a (page_base (hh + n))

/// ---------------------------------------------------------------------------
/// Carving a block of a swept run
/// ---------------------------------------------------------------------------

/// The cell `c` is a free block of the swept run at `hh`.
let cell_facts (g: heap) (pm: page_map) (c: obj_addr) (hh: nat{hh < n_pages}) (wz: nat) : prop =
  LargeHead? (entry pm hh).kind /\ (entry pm hh).swept == true /\
  (let n = run_len (entry pm hh).kind in
   let a = U64.v c - 8 in
   run_shape g hh n /\ run_swept_ok g pm hh /\
   steps_to g z a /\ steps_to g (page_base hh) a /\
   a + words_at g a * 8 <= page_base (hh + n) /\ page_base (hh + n) <= heap_size /\
   color_at g a == Blue /\ a % 8 == 0 /\ words_at g a == whsize g c /\
   wz + 1 <= whsize g c /\ wz >= 1)

/// What the carve starts from: the cell, and the heap well formed page by
/// page.
let carve_pre (g: heap) (st: pstate) (c: obj_addr) (hh: nat{hh < n_pages}) (wz: nat) : prop =
  map_ok st.pm /\ page_local_all g st.pm /\ tail_shape g /\
  well_formed_heap g /\ Mark.no_pointer_to_blue g /\
  cell_facts g st.pm c hh wz

let cell_bounds (g: heap) (pm: page_map) (c: obj_addr) (hh: nat{hh < n_pages}) (wz: nat)
  : Lemma (requires cell_facts g pm c hh wz)
          (ensures wz < pow2 54 /\ whsize g c - (wz + 1) <= pow2 54 /\
                   U64.v c - 8 + whsize g c * 8 <= heap_size)
  = assert (heap_size < pow2 57);
    FStar.Math.Lemmas.pow2_le_compat 57 54

/// The carve, as a replacement of the block.
let carve_replaces0 (g: heap) (h w: nat) (wz: nat)
  : Lemma (requires h % 8 == 0 /\ h + w * 8 <= heap_size /\ wz + 1 <= w /\ wz < pow2 54 /\
                    w - (wz + 1) <= pow2 54 /\
                    steps_to g z h /\ words_at g h == w /\ color_at g h == Blue)
          (ensures (let l = w - (wz + 1) in
                    let g' = carve_heap g h l wz in
                    replaces g g' h (h + w * 8) /\ layout_ok g' h (h + w * 8)))
  = let l = w - (wz + 1) in
    let e = h + w * 8 in
    carve_layout g h l wz;
    block_steps g h w;
    let old (b: nat) : Lemma (requires steps_to g h b /\ b < e) (ensures color_at g b == Blue)
      = one_block_pos g h b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires old)

let carve_replaces (g: heap) (pm: page_map) (c: obj_addr) (hh: nat{hh < n_pages}) (wz: nat)
  : Lemma (requires cell_facts g pm c hh wz)
          (ensures (let h = U64.v c - 8 in
                    let l = whsize g c - (wz + 1) in
                    let e = h + whsize g c * 8 in
                    wz < pow2 54 /\ l <= pow2 54 /\
                    replaces g (carve_heap g h l wz) h e /\
                    run_ctx g (carve_heap g h l wz) pm hh h e))
  = let h = U64.v c - 8 in
    let w = whsize g c in
    cell_bounds g pm c hh wz;
    carve_replaces0 g h w wz;
    steps_to_le g (page_base hh) h

/// An object whose header lies inside a free block the walk reaches is
/// that block.
let inside_free_blue (g: heap) (h: nat) (x: obj_addr)
  : Lemma (requires steps_to g z h /\ color_at g h == Blue /\
                    h <= U64.v x - 8 /\ U64.v x - 8 < h + words_at g h * 8)
          (ensures Seq.mem x (objects zero_addr g) ==> is_blue x g)
  = obj_iff g x;
    if Seq.mem x (objects zero_addr g) then begin
      steps_to_det g z h (U64.v x - 8);
      one_block_pos g h (U64.v x - 8);
      hdr_obj g x;
      is_blue_iff x g
    end

/// The object the carve returns.
let carve_object0 (g: heap) (h w: nat) (wz: nat)
  : Lemma (requires h % 8 == 0 /\ h + w * 8 <= heap_size /\ wz + 1 <= w /\ wz < pow2 54 /\
                    w - (wz + 1) <= pow2 54 /\ wz >= 1 /\
                    steps_to g z h /\ words_at g h == w /\ color_at g h == Blue)
          (ensures (let l = w - (wz + 1) in
                    let g' = carve_heap g h l wz in
                    let obj = obj_at (h + l * 8 + 8) in
                    obj =!= 0UL /\ U64.v obj >= 8 /\ U64.v obj < heap_size /\ U64.v obj % 8 == 0 /\
                    (let x : obj_addr = obj in
                     Seq.mem x (objects zero_addr g') /\
                     U64.v (wosize_of_object x g') == wz /\
                     is_white x g' /\
                     ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)))))
  = let l = w - (wz + 1) in
    let e = h + w * 8 in
    let g' = carve_heap g h l wz in
    carve_basic g h l wz;
    carve_steps_o g h l wz;
    let o = h + l * 8 in
    assert (o + 16 <= e);
    obj_at_spec (o + 8);
    let x : obj_addr = obj_at (o + 8) in
    hd_address_spec x;
    steps_to_frame g g' z h;
    steps_to_trans g' z h o;
    obj_iff g' x;
    hdr_obj g' x;
    is_white_iff x g';
    inside_free_blue g h x

let carve_object (g: heap) (pm: page_map) (c: obj_addr) (hh: nat{hh < n_pages}) (wz: nat)
  : Lemma (requires cell_facts g pm c hh wz)
          (ensures (let h = U64.v c - 8 in
                    let l = whsize g c - (wz + 1) in
                    wz < pow2 54 /\ l <= pow2 54 /\
                    (let g' = carve_heap g h l wz in
                     let obj = obj_at (h + l * 8 + 8) in
                     obj =!= 0UL /\ U64.v obj >= 8 /\ U64.v obj < heap_size /\ U64.v obj % 8 == 0 /\
                     (let x : obj_addr = obj in
                      Seq.mem x (objects zero_addr g') /\
                      U64.v (wosize_of_object x g') == wz /\
                      is_white x g' /\
                      ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))))))
  = cell_bounds g pm c hh wz;
    carve_object0 g (U64.v c - 8) (whsize g c) wz

/// **Carving keeps the page-local clauses and well-formedness.**
let carve_region (g: heap) (st: pstate) (c: obj_addr) (hh: nat{hh < n_pages}) (wz: nat)
  : Lemma (requires carve_pre g st c hh wz)
          (ensures (let h = U64.v c - 8 in
                    let l = whsize g c - (wz + 1) in
                    wz < pow2 54 /\ l <= pow2 54 /\
                    (let g' = carve_heap g h l wz in
                     page_local_all g' st.pm /\ tail_shape g' /\ well_formed_heap g' /\
                     Mark.no_pointer_to_blue g' /\ others_unchanged g g' /\
                     unswept_unchanged g g' st st)))
  = let h = U64.v c - 8 in
    let w = whsize g c in
    let l = w - (wz + 1) in
    carve_replaces g st.pm c hh wz;
    run_region_step g (carve_heap g h l wz) st hh h (h + w * 8)

/// ---------------------------------------------------------------------------
/// Cells around the carve
/// ---------------------------------------------------------------------------

/// The run facts of a free block of a swept run, from the page-local clauses.
let cell_facts_intro (g: heap) (pm: page_map) (c: obj_addr) (hh: nat{hh < n_pages}) (wz: nat)
  : Lemma (requires map_ok pm /\ page_local_all g pm /\ tail_shape g /\
                    LargeHead? (entry pm hh).kind /\ (entry pm hh).swept == true /\
                    page_base hh <= U64.v c - 8 /\
                    U64.v c - 8 < page_base (hh + run_len (entry pm hh).kind) /\
                    Seq.mem c (objects zero_addr g) /\ is_blue c g /\
                    wz + 1 <= whsize g c /\ wz >= 1)
          (ensures cell_facts g pm c hh wz)
  = let n = run_len (entry pm hh).kind in
    let a = U64.v c - 8 in
    assert (page_local g pm hh);
    assert (run_ok pm hh);
    assert (shape_ok g pm);
    assert (walk_page pm hh);
    walk_pages_reached g pm hh;
    page_base_mono (hh + n) n_pages;
    obj_iff g c;
    hdr_obj g c;
    is_blue_iff c g;
    steps_to_det g z (page_base hh) a;
    block_before g (page_base hh) a (page_base (hh + n))

/// A cell lies in a swept run.
let cell_run (g: heap) (st: pstate) (y: obj_addr)
  : Lemma (requires large_listable g st.pm y)
          (ensures exists (hh: nat{hh < n_pages}).
                     LargeHead? (entry st.pm hh).kind /\ (entry st.pm hh).swept == true /\
                     page_base hh <= U64.v y - 8 /\
                     U64.v y - 8 < page_base (hh + run_len (entry st.pm hh).kind))
  = hd_address_spec y

/// An object outside a replaced stretch keeps its header and link.
let out_same (g g': heap) (a e: nat) (y: obj_addr)
  : Lemma (requires replaces g g' a e /\ Seq.mem y (objects zero_addr g) /\
                    (U64.v y - 8 < a \/ U64.v y - 8 >= e))
          (ensures Seq.mem y (objects zero_addr g') /\
                   read_word g' (hd_address y) == read_word g (hd_address y) /\
                   is_blue y g' == is_blue y g /\ whsize g' y == whsize g y /\
                   (U64.v (wosize_of_object y g) >= 1 ==>
                      read_word g' (y <: hp_addr) == read_word g (y <: hp_addr)))
  = hd_address_spec y;
    replace_obj_out g g' a e y;
    hdr_obj g y;
    color_of_header_eq y g g';
    wosize_of_object_spec y g;
    wosize_of_object_spec y g'

/// An object of the new heap outside the stretch was an object before.
let out_back (g g': heap) (a e: nat) (y: obj_addr)
  : Lemma (requires replaces g g' a e /\ Seq.mem y (objects zero_addr g') /\
                    (U64.v y - 8 < a \/ U64.v y - 8 >= e))
          (ensures Seq.mem y (objects zero_addr g) /\
                   is_blue y g' == is_blue y g /\ whsize g' y == whsize g y)
  = hd_address_spec y;
    replace_obj_out g g' a e y;
    out_same g g' a e y

/// An object with its header inside a stretch the walk covers is one of its
/// blocks.
let in_stretch (g: heap) (a e: nat) (y: obj_addr)
  : Lemma (requires steps_to g z a /\ steps_to g a e /\ e <= heap_size /\
                    Seq.mem y (objects zero_addr g) /\ a <= U64.v y - 8 /\ U64.v y - 8 < e)
          (ensures steps_to g a (U64.v y - 8))
  = replace_obj_in g a e y

/// In the carved block, the objects are the remainder, at `c`, and the new
/// object, which is white.
let carved_objects (g: heap) (h w wz: nat) (y: obj_addr)
  : Lemma (requires h % 8 == 0 /\ h + w * 8 <= heap_size /\ wz + 1 <= w /\ wz < pow2 54 /\
                    w - (wz + 1) <= pow2 54 /\ steps_to g z h /\
                    Seq.mem y (objects zero_addr (carve_heap g h (w - (wz + 1)) wz)) /\
                    h <= U64.v y - 8 /\ U64.v y - 8 < h + w * 8)
          (ensures (let g' = carve_heap g h (w - (wz + 1)) wz in
                    (U64.v y - 8 == h /\ w - (wz + 1) >= 1 /\
                     is_blue y g' /\ whsize g' y == w - (wz + 1)) \/
                    is_white y g'))
  = let l = w - (wz + 1) in
    let g' = carve_heap g h l wz in
    carve_basic g h l wz;
    carve_walk g h l wz;
    steps_to_frame g g' z h;
    in_stretch g' h (h + w * 8) y;
    hdr_obj g' y;
    is_blue_iff y g';
    is_white_iff y g'

/// ---------------------------------------------------------------------------
/// The remainder stays on the list
/// ---------------------------------------------------------------------------

let in_cs_A (g: heap) (st: pstate) (cs: list obj_addr) (c: obj_addr) (wz: nat) (y: obj_addr)
  : Lemma (requires lview g st cs /\ L.mem c cs /\ L.mem y cs /\
                    (let h = U64.v c - 8 in let w = whsize g c in
                     h % 8 == 0 /\ h + w * 8 <= heap_size /\ wz < pow2 54 /\
                     w - (wz + 1) <= pow2 54 /\ w - (wz + 1) >= lg_min /\ steps_to g z h /\
                     replaces g (carve_heap g h (w - (wz + 1)) wz) h (h + w * 8)))
          (ensures (let h = U64.v c - 8 in let w = whsize g c in
                    let g' = carve_heap g h (w - (wz + 1)) wz in
                    Seq.mem y (objects zero_addr g') /\ U64.v (wosize_of_object y g') >= 1 /\
                    read_word g' (y <: hp_addr) == read_word g (y <: hp_addr) /\
                    is_blue y g' /\ large_listable g' st.pm y))
  = let h = U64.v c - 8 in
    let w = whsize g c in
    let l = w - (wz + 1) in
    let g' = carve_heap g h l wz in
    cells_mem g (large_head st) cs y;
    hd_address_spec y;
    hd_address_spec c;
    if y = c then begin
      carve_basic g h l wz;
      carve_walk g h l wz;
      steps_to_frame g g' z h;
      hdr_obj g c;
      obj_iff g' c;
      hdr_obj g' c;
      is_blue_iff c g';
      assert (mk_hp_addr (h + 8) == (c <: hp_addr))
    end else begin
      if h <= U64.v y - 8 && U64.v y - 8 < h + w * 8 then begin
        in_stretch g h (h + w * 8) y;
        hdr_obj g c;
        one_block_pos g h (U64.v y - 8)
      end;
      out_same g g' h (h + w * 8) y
    end

let complete_A (g: heap) (st: pstate) (cs: list obj_addr) (c: obj_addr) (wz: nat) (y: obj_addr)
  : Lemma (requires lview g st cs /\ L.mem c cs /\
                    (let h = U64.v c - 8 in let w = whsize g c in
                     h % 8 == 0 /\ h + w * 8 <= heap_size /\ wz + 1 <= w /\ wz < pow2 54 /\
                     w - (wz + 1) <= pow2 54 /\ steps_to g z h /\
                     replaces g (carve_heap g h (w - (wz + 1)) wz) h (h + w * 8) /\
                     (let g' = carve_heap g h (w - (wz + 1)) wz in
                      Seq.mem y (objects zero_addr g') /\ is_blue y g' /\
                      large_listable g' st.pm y)))
          (ensures L.mem y cs)
  = let h = U64.v c - 8 in
    let w = whsize g c in
    let g' = carve_heap g h (w - (wz + 1)) wz in
    hd_address_spec y;
    hd_address_spec c;
    if h <= U64.v y - 8 && U64.v y - 8 < h + w * 8 then begin
      carved_objects g h w wz y;
      is_blue_iff y g';
      is_white_iff y g'
    end else
      out_back g g' h (h + w * 8) y

let lists_A (g: heap) (st: pstate) (cs: list obj_addr) (c: obj_addr) (wz: nat)
  : Lemma (requires lview g st cs /\ L.mem c cs /\
                    (let h = U64.v c - 8 in let w = whsize g c in
                     h % 8 == 0 /\ h + w * 8 <= heap_size /\ wz < pow2 54 /\ wz + 1 <= w /\
                     w - (wz + 1) <= pow2 54 /\ w - (wz + 1) >= lg_min /\ steps_to g z h /\
                     replaces g (carve_heap g h (w - (wz + 1)) wz) h (h + w * 8)))
          (ensures lview (carve_heap g (U64.v c - 8) (whsize g c - (wz + 1)) wz) st cs)
  = let g' = carve_heap g (U64.v c - 8) (whsize g c - (wz + 1)) wz in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (in_cs_A g st cs c wz));
    cells_frame g g' (large_head st) cs;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (complete_A g st cs c wz))

/// ---------------------------------------------------------------------------
/// Unlinking
/// ---------------------------------------------------------------------------

#push-options "--fuel 2"
let rec last_mem (l: list obj_addr)
  : Lemma (requires Cons? l) (ensures L.mem (L.last l) l) (decreases l)
  = match l with
    | [_] -> ()
    | _ :: tl -> last_mem tl

/// The chain without `c`: the link of the cell before it, or the head, now
/// points past it.
let rec cells_unlink (g g': heap) (fp: U64.t) (pre: list obj_addr) (c: obj_addr) (post: list obj_addr)
  : Lemma (requires cells g fp (pre @ (c :: post)) /\ L.noRepeats pre /\
                    (forall (y: obj_addr). L.mem y pre \/ L.mem y post ==>
                       Seq.mem y (objects zero_addr g') /\ U64.v (wosize_of_object y g') >= 1) /\
                    (forall (y: obj_addr). L.mem y post ==>
                       read_word g' (y <: hp_addr) == read_word g (y <: hp_addr)) /\
                    (forall (y: obj_addr). L.mem y pre /\ y <> L.last pre ==>
                       read_word g' (y <: hp_addr) == read_word g (y <: hp_addr)) /\
                    (Cons? pre ==> read_word g' (L.last pre <: hp_addr) == read_word g (c <: hp_addr)))
          (ensures cells g' (if Nil? pre then read_word g (c <: hp_addr) else fp) (pre @ post))
          (decreases pre)
  = match pre with
    | [] -> cells_frame g g' (read_word g (c <: hp_addr)) post
    | [p] -> cells_frame g g' (read_word g (c <: hp_addr)) post
    | p :: pre' ->
      last_mem pre';
      cells_unlink g g' (read_word g (p <: hp_addr)) pre' c post
#pop-options

#push-options "--fuel 1"
let cells_cons (g: heap) (fp: U64.t) (c: obj_addr) (post: list obj_addr)
  : Lemma (requires cells g fp (c :: post))
          (ensures fp == (c <: U64.t) /\ cells g (read_word g (c <: hp_addr)) post)
  = ()

let mem_cons_obj (x c: obj_addr) (post: list obj_addr)
  : Lemma (L.mem x (c :: post) <==> (x == c \/ L.mem x post))
  = ()

let norep_cons (c: obj_addr) (post: list obj_addr)
  : Lemma (L.noRepeats (c :: post) <==> (~(L.mem c post) /\ L.noRepeats post))
  = ()

let length_cons (c: obj_addr) (post: list obj_addr)
  : Lemma (L.length (c :: post) == 1 + L.length post)
  = ()
#pop-options

let noRepeats_drop (pre: list obj_addr) (c: obj_addr) (post: list obj_addr)
  : Lemma (requires L.noRepeats (pre @ (c :: post)))
          (ensures L.noRepeats (pre @ post) /\ L.noRepeats pre /\ ~(L.mem c pre) /\ ~(L.mem c post) /\
                   (forall (x: obj_addr). L.mem x pre ==> ~(L.mem x post)) /\
                   L.length (pre @ post) < L.length (pre @ (c :: post)))
  = FStar.List.Tot.Properties.noRepeats_append_elim pre (c :: post);
    norep_cons c post;
    FStar.Classical.forall_intro (fun x -> mem_cons_obj x c post);
    FStar.List.Tot.Properties.noRepeats_append_intro pre post;
    FStar.List.Tot.Properties.append_length pre post;
    FStar.List.Tot.Properties.append_length pre (c :: post);
    length_cons c post

/// Rewriting the link of a free block is a replacement of that block.
let link_replaces (g: heap) (p: obj_addr) (v: U64.t)
  : Lemma (requires Seq.mem p (objects zero_addr g) /\ is_blue p g /\
                    U64.v (wosize_of_object p g) >= 1 /\ well_formed_heap_part4 g)
          (ensures (let a = U64.v p - 8 in
                    let e = a + whsize g p * 8 in
                    replaces g (wr g (U64.v p) v) a e /\ layout_ok (wr g (U64.v p) v) a e /\
                    read_word (wr g (U64.v p) v) (p <: hp_addr) == v /\
                    hdr (wr g (U64.v p) v) a == hdr g a))
  = let a = U64.v p - 8 in
    let g1 = wr g (U64.v p) v in
    let e = a + whsize g p * 8 in
    hd_address_spec p;
    obj_iff g p;
    hdr_obj g p;
    is_blue_iff p g;
    is_infix_spec p g;
    infix_tag_val ();
    FStar.Classical.forall_intro (wr_read g (U64.v p) v);
    assert (hdr g1 a == hdr g a);
    block_steps g a (whsize g p);
    block_steps g1 a (whsize g p);
    let pos (b: nat) : Lemma (requires steps_to g1 a b /\ b < e) (ensures b == a)
      = one_block_pos g1 a b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires pos);
    let old (b: nat) : Lemma (requires steps_to g a b /\ b < e) (ensures b == a)
      = one_block_pos g a b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires old)

/// ---------------------------------------------------------------------------
/// Case A: the remainder stays listed
/// ---------------------------------------------------------------------------

/// The cell `c` of the list lies in some swept run; its run facts.
let cell_of_list (g: heap) (st: pstate) (cs: list obj_addr) (c: obj_addr) (wz: nat)
  : Lemma (requires pages_ok g st /\ lview g st cs /\ L.mem c cs /\ wz + 1 <= whsize g c /\ wz >= 1)
          (ensures exists (hh: nat{hh < n_pages}). cell_facts g st.pm c hh wz)
  = pages_ok_elim g st;
    cells_mem g (large_head st) cs c;
    cell_run g st c;
    eliminate exists (hh: nat{hh < n_pages}).
      LargeHead? (entry st.pm hh).kind /\ (entry st.pm hh).swept == true /\
      page_base hh <= U64.v c - 8 /\ U64.v c - 8 < page_base (hh + run_len (entry st.pm hh).kind)
    with cell_facts_intro g st.pm c hh wz

let carve_A_ok (g: heap) (st: pstate) (cs: list obj_addr) (c: obj_addr) (hh: nat{hh < n_pages})
               (wz: nat{wz < pow2 54})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ lview g st cs /\ L.mem c cs /\
                    cell_facts g st.pm c hh wz /\ rem_of g c wz >= lg_min)
          (ensures alloc_ok g (carved g c wz) st st wz (obj_of g c wz))
  = let h = U64.v c - 8 in
    let w = whsize g c in
    let l = w - (wz + 1) in
    let g' = carve_heap g h l wz in
    pages_ok_elim g st;
    cell_bounds g st.pm c hh wz;
    carve_replaces g st.pm c hh wz;
    carve_region g st c hh wz;
    carve_object g st.pm c hh wz;
    lists_A g st cs c wz;
    lview_large_ok g' st cs;
    pages_ok_intro g' st

/// ---------------------------------------------------------------------------
/// Case B: the block leaves the list
/// ---------------------------------------------------------------------------

/// A cell other than `c` survives the carve of `c`.
let kept_carve (g1 g': heap) (c: obj_addr) (wz: nat) (y: obj_addr)
  : Lemma (requires (let h = U64.v c - 8 in let w = whsize g1 c in
                     wz + 1 <= w /\ wz < pow2 54 /\ w - (wz + 1) <= pow2 54 /\
                     g' == carve_heap g1 h (w - (wz + 1)) wz /\
                     replaces g1 g' h (h + w * 8) /\
                     Seq.mem y (objects zero_addr g1) /\ y <> c /\ color_at g1 h == Blue /\
                     words_at g1 h == w))
          (ensures Seq.mem y (objects zero_addr g') /\
                   read_word g' (hd_address y) == read_word g1 (hd_address y) /\
                   is_blue y g' == is_blue y g1 /\ whsize g' y == whsize g1 y /\
                   (U64.v (wosize_of_object y g1) >= 1 ==>
                      read_word g' (y <: hp_addr) == read_word g1 (y <: hp_addr)))
  = let h = U64.v c - 8 in
    let w = whsize g1 c in
    hd_address_spec y;
    hd_address_spec c;
    if h <= U64.v y - 8 && U64.v y - 8 < h + w * 8 then begin
      in_stretch g1 h (h + w * 8) y;
      one_block_pos g1 h (U64.v y - 8)
    end;
    out_same g1 g' h (h + w * 8) y

/// A free listable block after the carve was a free listable block before,
/// other than `c`.
let back_carve (g1 g': heap) (pm: page_map) (c: obj_addr) (wz: nat) (y: obj_addr)
  : Lemma (requires (let h = U64.v c - 8 in let w = whsize g1 c in
                     wz + 1 <= w /\ wz < pow2 54 /\ w - (wz + 1) <= pow2 54 /\
                     w - (wz + 1) < lg_min /\ h % 8 == 0 /\ h + w * 8 <= heap_size /\
                     g' == carve_heap g1 h (w - (wz + 1)) wz /\ steps_to g1 z h /\
                     replaces g1 g' h (h + w * 8) /\
                     Seq.mem y (objects zero_addr g') /\ is_blue y g' /\ large_listable g' pm y))
          (ensures Seq.mem y (objects zero_addr g1) /\ y <> c /\ is_blue y g1 /\
                   large_listable g1 pm y)
  = let h = U64.v c - 8 in
    let w = whsize g1 c in
    hd_address_spec y;
    hd_address_spec c;
    if h <= U64.v y - 8 && U64.v y - 8 < h + w * 8 then begin
      carved_objects g1 h w wz y;
      is_blue_iff y g';
      is_white_iff y g'
    end else
      out_back g1 g' h (h + w * 8) y

let lists_B0 (g: heap) (st: pstate) (c: obj_addr) (post: list obj_addr) (wz: nat)
  : Lemma (requires lview g st (c :: post) /\
                    (let h = U64.v c - 8 in let w = whsize g c in
                     h % 8 == 0 /\ h + w * 8 <= heap_size /\ wz < pow2 54 /\ wz + 1 <= w /\
                     w - (wz + 1) <= pow2 54 /\ w - (wz + 1) < lg_min /\ steps_to g z h /\
                     color_at g h == Blue /\ words_at g h == w /\
                     replaces g (carve_heap g h (w - (wz + 1)) wz) h (h + w * 8)))
          (ensures lview (carve_heap g (U64.v c - 8) (whsize g c - (wz + 1)) wz)
                         { st with large = FLs.fls_set st.large 0 (read_word g (c <: hp_addr)) } post)
  = let g' = carve_heap g (U64.v c - 8) (whsize g c - (wz + 1)) wz in
    let st' = { st with large = FLs.fls_set st.large 0 (read_word g (c <: hp_addr)) } in
    norep_cons c post;
    cells_cons g (large_head st) c post;
    length_cons c post;
    let kept (y: obj_addr)
      : Lemma (requires L.mem y post)
              (ensures Seq.mem y (objects zero_addr g') /\ U64.v (wosize_of_object y g') >= 1 /\
                       read_word g' (y <: hp_addr) == read_word g (y <: hp_addr) /\
                       is_blue y g' /\ large_listable g' st'.pm y)
      = mem_cons_obj y c post;
        cells_mem g (large_head st) (c :: post) y;
        kept_carve g g' c wz y;
        wosize_of_object_spec y g;
        wosize_of_object_spec y g'
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires kept);
    cells_frame g g' (read_word g (c <: hp_addr)) post;
    let back (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g') /\ is_blue y g' /\ large_listable g' st'.pm y)
              (ensures L.mem y post)
      = back_carve g g' st.pm c wz y;
        mem_cons_obj y c post
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires back)

/// A cell survives the rewrite of the link of the cell `p`.
let kept_link (g g1: heap) (p: obj_addr) (v: U64.t) (y: obj_addr)
  : Lemma (requires g1 == wr g (U64.v p) v /\
                    replaces g g1 (U64.v p - 8) (U64.v p - 8 + whsize g p * 8) /\
                    hdr g1 (U64.v p - 8) == hdr g (U64.v p - 8) /\
                    read_word g1 (p <: hp_addr) == v /\
                    Seq.mem y (objects zero_addr g) /\ Seq.mem p (objects zero_addr g) /\
                    words_at g (U64.v p - 8) == whsize g p)
          (ensures Seq.mem y (objects zero_addr g1) /\
                   is_blue y g1 == is_blue y g /\ whsize g1 y == whsize g y /\
                   (U64.v (wosize_of_object y g) >= 1 ==>
                      read_word g1 (y <: hp_addr) == (if y = p then v else read_word g (y <: hp_addr))))
  = let a = U64.v p - 8 in
    let e = a + whsize g p * 8 in
    hd_address_spec y;
    hd_address_spec p;
    if y = p then begin
      replaces_frame_prefix g g1 a e;
      obj_iff g p;
      obj_iff g1 p;
      hdr_obj g p;
      hdr_obj g1 p;
      color_of_header_eq p g g1;
      wosize_of_object_spec p g;
      wosize_of_object_spec p g1
    end else begin
      if a <= U64.v y - 8 && U64.v y - 8 < e then begin
        obj_iff g p;
        in_stretch g a e y;
        one_block_pos g a (U64.v y - 8)
      end;
      out_same g g1 a e y
    end

/// A free listable block after the link rewrite was one before.
let back_link (g g1: heap) (pm: page_map) (p: obj_addr) (v: U64.t) (y: obj_addr)
  : Lemma (requires g1 == wr g (U64.v p) v /\
                    replaces g g1 (U64.v p - 8) (U64.v p - 8 + whsize g p * 8) /\
                    hdr g1 (U64.v p - 8) == hdr g (U64.v p - 8) /\
                    Seq.mem p (objects zero_addr g) /\
                    Seq.mem y (objects zero_addr g1) /\ is_blue y g1 /\ large_listable g1 pm y)
          (ensures Seq.mem y (objects zero_addr g) /\ is_blue y g /\ large_listable g pm y)
  = let a = U64.v p - 8 in
    let e = a + whsize g p * 8 in
    hd_address_spec y;
    hd_address_spec p;
    obj_iff g p;
    hdr_obj g p;
    if a <= U64.v y - 8 && U64.v y - 8 < e then begin
      assert (words_at g1 a == words_at g a);
      replaces_frame_prefix g g1 a e;
      in_stretch g1 a e y;
      one_block_pos g1 a (U64.v y - 8);
      assert (y == p);
      kept_link g g1 p v p
    end else
      out_back g g1 a e y

/// The context of an unlink through the link of the cell `p`, then the
/// carve of `c` in the heap `g1` that results.
let unlink_ctx (g g1 g': heap) (st: pstate) (pre: list obj_addr) (c: obj_addr) (post: list obj_addr)
               (wz: nat) : prop =
  Cons? pre /\ wz < pow2 54 /\
  lview g st (pre @ (c :: post)) /\
  (let p = L.last pre in
   let nx = read_word g (c <: hp_addr) in
   let h = U64.v c - 8 in
   let w = whsize g c in
   g1 == wr g (U64.v p) nx /\
   replaces g g1 (U64.v p - 8) (U64.v p - 8 + whsize g p * 8) /\
   hdr g1 (U64.v p - 8) == hdr g (U64.v p - 8) /\
   read_word g1 (p <: hp_addr) == nx /\
   Seq.mem p (objects zero_addr g) /\ words_at g (U64.v p - 8) == whsize g p /\
   whsize g1 c == w /\ wz + 1 <= w /\ w - (wz + 1) <= pow2 54 /\ w - (wz + 1) < lg_min /\
   h % 8 == 0 /\ h + w * 8 <= heap_size /\
   g' == carve_heap g1 h (w - (wz + 1)) wz /\ steps_to g1 z h /\
   color_at g1 h == Blue /\ words_at g1 h == w /\
   replaces g1 g' h (h + w * 8))

let lists_B (g g1 g': heap) (st: pstate) (pre: list obj_addr) (c: obj_addr) (post: list obj_addr)
            (wz: nat)
  : Lemma (requires unlink_ctx g g1 g' st pre c post wz)
          (ensures lview g' st (pre @ post))
  = let cs = pre @ (c :: post) in
    let p = L.last pre in
    let nx = read_word g (c <: hp_addr) in
    noRepeats_drop pre c post;
    last_mem pre;
    FStar.List.Tot.Properties.append_mem_forall pre (c :: post);
    FStar.List.Tot.Properties.append_mem_forall pre post;
    FStar.Classical.forall_intro (fun y -> mem_cons_obj y c post);
    let kept (y: obj_addr)
      : Lemma (requires L.mem y pre \/ L.mem y post)
              (ensures Seq.mem y (objects zero_addr g') /\ U64.v (wosize_of_object y g') >= 1 /\
                       read_word g' (y <: hp_addr) ==
                         (if y = p then read_word g (c <: hp_addr) else read_word g (y <: hp_addr)) /\
                       is_blue y g' /\ large_listable g' st.pm y)
      = cells_mem g (large_head st) cs y;
        cells_mem g (large_head st) cs p;
        kept_link g g1 p nx y;
        kept_carve g1 g' c wz y;
        wosize_of_object_spec y g;
        wosize_of_object_spec y g1;
        wosize_of_object_spec y g'
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires kept);
    cells_unlink g g' (large_head st) pre c post;
    let back (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g') /\ is_blue y g' /\ large_listable g' st.pm y)
              (ensures L.mem y (pre @ post))
      = back_carve g1 g' st.pm c wz y;
        back_link g g1 st.pm p nx y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires back)

let wfh_part4 (g: heap)
  : Lemma (requires well_formed_heap g) (ensures well_formed_heap_part4 g)
  = reveal_opaque (`%well_formed_heap) well_formed_heap

/// The block is first on the list: the head moves past it.
let carve_B_head (g: heap) (st: pstate) (c: obj_addr) (post: list obj_addr) (hh: nat{hh < n_pages})
                 (wz: nat{wz < pow2 54})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ lview g st (c :: post) /\
                    cell_facts g st.pm c hh wz /\ rem_of g c wz < lg_min)
          (ensures (let st' = { st with large = FLs.fls_set st.large 0 (read_word g (c <: hp_addr)) } in
                    alloc_ok g (carved g c wz) st st' wz (obj_of g c wz)))
  = let st' = { st with large = FLs.fls_set st.large 0 (read_word g (c <: hp_addr)) } in
    let g' = carved g c wz in
    pages_ok_elim g st;
    cell_bounds g st.pm c hh wz;
    carve_replaces g st.pm c hh wz;
    carve_region g st c hh wz;
    carve_object g st.pm c hh wz;
    lists_B0 g st c post wz;
    lview_large_ok g' st' post;
    assert (avail_ok st');
    pages_ok_intro g' st'

/// The run facts of the cell before `c`, and the rewrite of its link.
let link_step (g: heap) (st: pstate) (cs: list obj_addr) (p: obj_addr) (v: U64.t)
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ lview g st cs /\ L.mem p cs)
          (ensures (let g1 = wr g (U64.v p) v in
                    let a = U64.v p - 8 in
                    replaces g g1 a (a + whsize g p * 8) /\ hdr g1 a == hdr g a /\
                    read_word g1 (p <: hp_addr) == v /\
                    Seq.mem p (objects zero_addr g) /\ words_at g a == whsize g p /\
                    page_local_all g1 st.pm /\ tail_shape g1 /\ well_formed_heap g1 /\
                    Mark.no_pointer_to_blue g1 /\ step_ok g g1 st st))
  = let g1 = wr g (U64.v p) v in
    let a = U64.v p - 8 in
    pages_ok_elim g st;
    cells_mem g (large_head st) cs p;
    wfh_part4 g;
    link_replaces g p v;
    hdr_obj g p;
    listable_class g st.pm p;
    params_ok ();
    cell_of_list g st cs p 1;
    eliminate exists (hh: nat{hh < n_pages}). cell_facts g st.pm p hh 1
    with begin
      steps_to_le g (page_base hh) a;
      run_region_step g g1 st hh a (a + whsize g p * 8)
    end

/// `alloc_ok` from its parts.
let alloc_ok_intro (g g': heap) (st st': pstate) (wz: nat) (obj: U64.t)
  : Lemma (requires obj =!= 0UL /\ U64.v obj >= 8 /\ U64.v obj < heap_size /\ U64.v obj % 8 == 0 /\
                    (let x : obj_addr = obj in
                     Seq.mem x (objects zero_addr g') /\
                     U64.v (wosize_of_object x g') == wz /\
                     is_white x g' /\
                     ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))) /\
                    map_ok st'.pm /\ page_local_all g' st'.pm /\ tail_shape g' /\
                    avail_ok st' /\ large_ok g' st' /\ Mark.no_pointer_to_blue g' /\
                    well_formed_heap g' /\ others_unchanged g g' /\ unswept_unchanged g g' st st')
          (ensures alloc_ok g g' st st' wz obj)
  = pages_ok_intro g' st'

/// The cell's run facts carry to a heap where it is the same free block and
/// the pages keep their clauses.
let cell_facts_move (g g1: heap) (pm: page_map) (c: obj_addr) (hh: nat{hh < n_pages}) (wz: nat)
  : Lemma (requires cell_facts g pm c hh wz /\ map_ok pm /\ page_local_all g1 pm /\ tail_shape g1 /\
                    Seq.mem c (objects zero_addr g1) /\ is_blue c g1 /\ whsize g1 c == whsize g c)
          (ensures cell_facts g1 pm c hh wz)
  = steps_to_le g (page_base hh) (U64.v c - 8);
    cell_facts_intro g1 pm c hh wz

/// The block follows the cell `p`: `p`'s link moves past it.
let carve_B_prev (g: heap) (st: pstate) (pre: list obj_addr) (c: obj_addr) (post: list obj_addr)
                 (wz: nat{wz < pow2 54})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ lview g st (pre @ (c :: post)) /\
                    Cons? pre /\ wz + 1 <= whsize g c /\ wz >= 1 /\ rem_of g c wz < lg_min)
          (ensures (let g1 = wr g (U64.v (L.last pre)) (read_word g (c <: hp_addr)) in
                    alloc_ok g (carved g1 c wz) st st wz (obj_of g1 c wz)))
  = let cs = pre @ (c :: post) in
    let p = L.last pre in
    let nx = read_word g (c <: hp_addr) in
    let g1 = wr g (U64.v p) nx in
    last_mem pre;
    noRepeats_drop pre c post;
    FStar.List.Tot.Properties.append_mem_forall pre (c :: post);
    FStar.Classical.forall_intro (fun y -> mem_cons_obj y c post);
    link_step g st cs p nx;
    cells_mem g (large_head st) cs c;
    kept_link g g1 p nx c;
    cell_of_list g st cs c wz;
    eliminate exists (hh: nat{hh < n_pages}). cell_facts g st.pm c hh wz
    with begin
      pages_ok_elim g st;
      cell_facts_move g g1 st.pm c hh wz;
      cell_bounds g1 st.pm c hh wz;
      carve_replaces g1 st.pm c hh wz;
      carve_region g1 st c hh wz;
      carve_object g1 st.pm c hh wz;
      let g' = carved g1 c wz in
      lists_B g g1 g' st pre c post wz;
      lview_large_ok g' st (pre @ post);
      alloc_ok_intro g1 g' st st wz (obj_of g1 c wz);
      alloc_ok_compose g g1 g' st st st wz (obj_of g1 c wz)
    end

/// **Carving from the large list is correct.**
let carve_ok (g: heap) (st: pstate) (pre: list obj_addr) (c: obj_addr) (post: list obj_addr)
             (wz: nat{wz < pow2 54})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ lview g st (pre @ (c :: post)) /\
                    wz + 1 <= whsize g c /\ wz >= 1)
          (ensures (let (g', st', obj) = carve g st pre c wz in alloc_ok g g' st st' wz obj))
  = let cs = pre @ (c :: post) in
    FStar.List.Tot.Properties.append_mem_forall pre (c :: post);
    mem_cons_obj c c post;
    if rem_of g c wz >= lg_min then begin
      cell_of_list g st cs c wz;
      eliminate exists (hh: nat{hh < n_pages}). cell_facts g st.pm c hh wz
      with carve_A_ok g st cs c hh wz
    end
    else match pre with
      | [] ->
        assert_norm ([] @ (c :: post) == c :: post);
        cell_of_list g st cs c wz;
        eliminate exists (hh: nat{hh < n_pages}). cell_facts g st.pm c hh wz
        with carve_B_head g st c post hh wz
      | _ -> carve_B_prev g st pre c post wz
