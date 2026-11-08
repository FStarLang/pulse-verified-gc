/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.NewRun - a new run for a large block
/// ---------------------------------------------------------------------------
///
/// When no listed block fits a large block of `w` words, the allocator takes
/// `k = pages_for w` consecutive free pages and makes them a new swept run:
///   - the object at the run's start, its fields cleared;
///   - the rest, `r = k * page_wsize - w` words, fewer than a page, one free
///     block after it;
///   - that block pushed on list 0 if it has at least `lg_min` words, and
///     left unlisted otherwise.
/// A new run is never joined to a neighbouring one: runs stay independent
/// for the sweep.
///
/// `new_run_ok` proves `alloc_ok` of the result.

module GC.Spec.Pages.NewRun

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
module Mark = GC.Spec.Mark
module FLs = GC.Spec.FreeLists
module AL = GC.Spec.Allocator.Lemmas
module Push = GC.Spec.FreeLists.Push
module LG = GC.Spec.Pages.Large

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The specification
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
/// Pages `i .. i + k - 1` are all free, as a test.
let rec all_free (pm: page_map) (i k: nat) : Tot bool (decreases k) =
  if k = 0 then i <= n_pages
  else i < n_pages && (entry pm i).kind = Free && all_free pm (i + 1) (k - 1)

/// The first `i` from `j` on with `k` free pages, or `n_pages`.
let rec find_run (pm: page_map) (k: pos) (j: nat)
  : Tot nat (decreases (if j <= n_pages then n_pages + 1 - j else 0))
  = if j + k > n_pages then n_pages
    else if all_free pm j k then j
    else find_run pm k (j + 1)
#pop-options

let head_entry (k: pos) : page_info =
  { kind = LargeHead k; swept = true; free_head = 0UL; nfree = 0; next = 0UL }

let cont_entry : page_info =
  { kind = LargeCont; swept = true; free_head = 0UL; nfree = 0; next = 0UL }

/// Pages `i .. i + k - 1` become a swept run.
let run_map (pm: page_map) (i: nat) (k: pos) : page_map =
  Seq.init n_pages (fun (j: nat{j < n_pages}) ->
    if j = i then head_entry k else if i < j && j < i + k then cont_entry else entry pm j)

/// The words a run of `k` pages has after an object of `w` words.
let rest (k: pos) (w: pos) : int = k * page_wsize - w

/// The heap of the new run.
let run_heap (g: heap) (i: nat) (k: pos) (wz: nat{wz < pow2 54}) (hd0: U64.t) : GTot heap =
  let a = page_base i in
  let w = wz + 1 in
  let r = rest k w in
  let g1 = put_obj g a wz in
  if r > 0 && r <= pow2 54 then begin
    let g2 = put_blue g1 (a + w * 8) r in
    if r >= lg_min then wr g2 (a + w * 8 + 8) hd0 else g2
  end
  else g1

let run_state (st: pstate) (i: nat) (k: pos) (w: pos) : pstate =
  let r = rest k w in
  { st with pm = run_map st.pm i k;
            large = (if r >= lg_min then FLs.fls_set st.large 0 (LG.obj_at (page_base i + w * 8 + 8))
                     else st.large) }

let new_run (g: heap) (st: pstate) (i: nat) (k: pos) (wz: nat{wz < pow2 54})
  : GTot (heap & pstate & U64.t)
  = (run_heap g i k wz (large_head st), run_state st i k (wz + 1), LG.obj_at (page_base i + 8))

/// ---------------------------------------------------------------------------
/// Arithmetic
/// ---------------------------------------------------------------------------

let pages_for_spec (w: pos)
  : Lemma ((pages_for w - 1) * page_wsize < w /\ w <= pages_for w * page_wsize)
  = FStar.Math.Lemmas.lemma_div_mod (w + page_wsize - 1) page_wsize;
    FStar.Math.Lemmas.distributivity_sub_left (pages_for w) 1 page_wsize

/// A run of `k` pages from page `i` spans `k * page_wsize` words.
let run_span (i: nat) (k: nat)
  : Lemma (page_base (i + k) == page_base i + k * page_wsize * 8)
  = FStar.Math.Lemmas.distributivity_add_left i k page_bytes;
    FStar.Math.Lemmas.paren_mul_right k page_wsize 8

#push-options "--fuel 1"
let rec all_free_spec (pm: page_map) (i k: nat)
  : Lemma (ensures all_free pm i k <==> free_run pm i k) (decreases k)
  = if k = 0 then () else all_free_spec pm (i + 1) (k - 1)

let rec find_run_spec (pm: page_map) (k: pos) (j: nat)
  : Lemma (ensures (let r = find_run pm k j in
                    (r + k <= n_pages ==> free_run pm r k) /\
                    (r + k > n_pages ==> (forall (i: nat). i >= j ==> ~(free_run pm i k)))))
          (decreases (if j <= n_pages then n_pages + 1 - j else 0))
  = all_free_spec pm j k;
    if j + k > n_pages then ()
    else if all_free pm j k then ()
    else find_run_spec pm k (j + 1)
#pop-options

/// ---------------------------------------------------------------------------
/// The free pages
/// ---------------------------------------------------------------------------

/// The walk over `k` free pages stops only at their starts, all free.
let rec free_pages_walk (g: heap) (pm: page_map) (i k: nat)
  : Lemma (requires i + k <= n_pages /\
                    (forall (j: nat). i <= j /\ j < i + k ==> free_page_shape g j))
          (ensures steps_to g (page_base i) (page_base (i + k)) /\
                   (forall (b: nat). steps_to g (page_base i) b /\ b < page_base (i + k) ==>
                      color_at g b == Blue))
          (decreases k)
  = if k = 0 then begin
      steps_to_refl g (page_base i);
      FStar.Classical.forall_intro (FStar.Classical.move_requires (steps_to_le g (page_base i)))
    end
    else begin
      free_page_steps g i;
      free_pages_walk g pm (i + 1) (k - 1);
      steps_to_trans g (page_base i) (page_base (i + 1)) (page_base (i + k));
      page_base_mono (i + 1) (i + k);
      let pos (b: nat)
        : Lemma (requires steps_to g (page_base i) b /\ b < page_base (i + k))
                (ensures color_at g b == Blue)
        = steps_to_le g (page_base i) b;
          if b < page_base (i + 1) then begin
            FStar.Math.Lemmas.distributivity_add_left i 1 page_bytes;
            one_block_pos g (page_base i) b
          end
          else steps_to_det g (page_base i) (page_base (i + 1)) b
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires pos)
    end

/// ---------------------------------------------------------------------------
/// The new run's heap
/// ---------------------------------------------------------------------------

let run_read (g: heap) (i: nat{i < n_pages}) (k: pos) (wz: nat{wz < pow2 54}) (hd0: U64.t) (x: hp_addr)
  : Lemma (requires rest k (wz + 1) >= 0 /\ rest k (wz + 1) <= pow2 54)
          (ensures (let a = page_base i in
                    let w = wz + 1 in
                    let r = rest k w in
                    read_word (run_heap g i k wz hd0) x ==
                    (if U64.v x = a then ohdr wz
                     else if a < U64.v x && U64.v x < a + w * 8 then 0UL
                     else if r > 0 && U64.v x = a + w * 8 then bhdr r
                     else if r >= lg_min && U64.v x = a + w * 8 + 8 then hd0
                     else read_word g x)))
  = let a = page_base i in
    let w = wz + 1 in
    let r = rest k w in
    page_base_aligned i;
    let g1 = put_obj g a wz in
    put_obj_read g a wz x;
    if r > 0 then begin
      let g2 = put_blue g1 (a + w * 8) r in
      wr_read g1 (a + w * 8) (bhdr r) x;
      if r >= lg_min then wr_read g2 (a + w * 8 + 8) hd0 x
    end

/// The layout of the new run: the object, then the rest as one free block.
let run_layout (g: heap) (i: nat{i < n_pages}) (k: pos) (wz: nat{wz < pow2 54}) (hd0: U64.t)
  : Lemma (requires i + k <= n_pages /\ rest k (wz + 1) >= 0 /\ rest k (wz + 1) < page_wsize /\
                    wz + 1 > small_max)
          (ensures (let g' = run_heap g i k wz hd0 in
                    let a = page_base i in
                    let w = wz + 1 in
                    let r = rest k w in
                    let e = page_base (i + k) in
                    e == a + (w + r) * 8 /\ e <= heap_size /\ a % 8 == 0 /\
                    (forall (x: hp_addr). U64.v x < a \/ U64.v x >= e ==> read_word g' x == read_word g x) /\
                    words_at g' a == w /\ color_at g' a == White /\
                    (r > 0 ==> words_at g' (a + w * 8) == r /\ color_at g' (a + w * 8) == Blue) /\
                    (r >= lg_min ==> read_word g' (mk_hp_addr (a + w * 8 + 8)) == hd0) /\
                    steps_to g' a e /\
                    (forall (b: nat). steps_to g' a b /\ b < e ==>
                       new_block_ok g' b /\ (b == a \/ (r > 0 /\ b == a + w * 8)))))
  = let g' = run_heap g i k wz hd0 in
    let a = page_base i in
    let w = wz + 1 in
    let r = rest k w in
    let e = page_base (i + k) in
    cls_bounds 0;
    FStar.Math.Lemmas.pow2_le_compat 54 20;
    run_span i k;
    page_base_mono (i + k) n_pages;
    page_base_aligned i;
    assert (e == a + (w + r) * 8);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (run_read g i k wz hd0));
    let fields (x: hp_addr) : Lemma (a < U64.v x /\ U64.v x < a + w * 8 ==> read_word g' x == 0UL)
      = run_read g i k wz hd0 x
    in
    FStar.Classical.forall_intro fields;
    run_read g i k wz hd0 (mk_hp_addr a);
    obj_block g' a wz;
    if r > 0 then begin
      aligned_plus_mul8 a w;
      run_read g i k wz hd0 (mk_hp_addr (a + w * 8));
      blue_block_ok g' (a + w * 8) r;
      if r >= lg_min then begin
        params_ok ();
        run_read g i k wz hd0 (mk_hp_addr (a + w * 8 + 8))
      end
    end;
    two_blocks g' a w r

/// ---------------------------------------------------------------------------
/// The page map of the new run
/// ---------------------------------------------------------------------------

let run_entry (pm: page_map) (i: nat) (k: pos) (j: nat{j < n_pages})
  : Lemma (entry (run_map pm i k) j ==
           (if j = i then head_entry k else if i < j && j < i + k then cont_entry else entry pm j))
  = Seq.init_index_ n_pages (fun (j: nat{j < n_pages}) ->
      if j = i then head_entry k else if i < j && j < i + k then cont_entry else entry pm j) j

let run_entries (pm: page_map) (i: nat) (k: pos)
  : Lemma (forall (j: nat{j < n_pages}). entry (run_map pm i k) j ==
             (if j = i then head_entry k else if i < j && j < i + k then cont_entry else entry pm j))
  = FStar.Classical.forall_intro (run_entry pm i k)

let run_map_ok (pm: page_map) (i: nat) (k: pos)
  : Lemma (requires map_ok pm /\ free_run pm i k)
          (ensures map_ok (run_map pm i k))
  = let pm' = run_map pm i k in
    run_entries pm i k;
    let aux (j: nat{j < n_pages}) : Lemma (run_ok pm' j /\ cont_ok pm' j /\ free_ok pm' j)
      = assert (run_ok pm j /\ cont_ok pm j /\ free_ok pm j);
        if (entry pm' j).kind = LargeCont && not (i < j && j < i + k) then
          eliminate exists (h: nat{h < n_pages}). h < j /\ in_run pm h j
          with assert (in_run pm' h j)
        else if (entry pm' j).kind = LargeCont then assert (in_run pm' i j)
    in
    FStar.Classical.forall_intro aux

/// The swept runs of the new map: the old ones, and the new run.
let run_swept (pm: page_map) (i: nat) (k: pos) (x: nat)
  : Lemma (requires map_ok pm /\ free_run pm i k)
          (ensures (in_swept_run pm x ==> in_swept_run (run_map pm i k) x) /\
                   (in_swept_run (run_map pm i k) x /\ (x < page_base i \/ x >= page_base (i + k)) ==>
                      in_swept_run pm x) /\
                   (page_base i <= x /\ x < page_base (i + k) ==>
                      in_swept_run (run_map pm i k) x /\ ~(in_swept_run pm x)))
  = let pm' = run_map pm i k in
    run_entries pm i k;
    if page_base i <= x && x < page_base (i + k) then begin
      assert (LargeHead? (entry pm' i).kind);
      page_base_mono (i + k) n_pages;
      page_of_spec x;
      in_pages i k (page_of x) x;
      FStar.Classical.move_requires (not_in_run pm (page_of x)) x
    end

/// ---------------------------------------------------------------------------
/// The new run is correct
/// ---------------------------------------------------------------------------

let nr_ctx (g: heap) (st: pstate) (i: nat) (k: pos) (wz: nat) : prop =
  pages_ok g st /\ well_formed_heap g /\ wz < pow2 54 /\ wz + 1 > small_max /\
  k == pages_for (wz + 1) /\ free_run st.pm i k

let nr_rest (g: heap) (st: pstate) (i: nat) (k: pos) (wz: nat)
  : Lemma (requires nr_ctx g st i k wz)
          (ensures rest k (wz + 1) >= 0 /\ rest k (wz + 1) < page_wsize /\ i < n_pages /\
                   i + k <= n_pages)
  = pages_for_spec (wz + 1);
    FStar.Math.Lemmas.distributivity_sub_left k 1 page_wsize

let nr_heap (g: heap) (st: pstate) (i: nat{i < n_pages}) (k: pos) (wz: nat{wz < pow2 54}) : GTot heap =
  run_heap g i k wz (large_head st)

let nr_replaces (g: heap) (st: pstate) (i: nat{i < n_pages}) (k: pos) (wz: nat{wz < pow2 54})
  : Lemma (requires nr_ctx g st i k wz)
          (ensures replaces g (nr_heap g st i k wz) (page_base i) (page_base (i + k)) /\
                   steps_to g z (page_base i))
  = nr_rest g st i k wz;
    pages_ok_elim g st;
    assert (walk_page st.pm i);
    walk_pages_reached g st.pm i;
    let fp (j: nat) : Lemma (i <= j /\ j < i + k ==> free_page_shape g j)
      = if i <= j && j < i + k then assert (page_local g st.pm j)
    in
    FStar.Classical.forall_intro fp;
    free_pages_walk g st.pm i k;
    run_layout g i k wz (large_head st)

/// The new run's own clauses.
let nr_page (g: heap) (st: pstate) (i: nat{i < n_pages}) (k: pos) (wz: nat{wz < pow2 54})
  : Lemma (requires nr_ctx g st i k wz)
          (ensures page_local (nr_heap g st i k wz) (run_map st.pm i k) i)
  = let g' = nr_heap g st i k wz in
    let pm' = run_map st.pm i k in
    nr_rest g st i k wz;
    run_entries st.pm i k;
    run_layout g i k wz (large_head st);
    let a = page_base i in
    let w = wz + 1 in
    let r = rest k w in
    let e = page_base (i + k) in
    let blk (b: nat)
      : Lemma (requires run_block g' i k b)
              (ensures (color_at g' b == White \/ color_at g' b == Blue) /\
                       (color_at g' b == Blue /\ b + words_at g' b * 8 < e ==>
                          color_at g' (b + words_at g' b * 8) =!= Blue) /\
                       (color_at g' b == Blue ==>
                          (forall (j: nat). i <= j /\ j < i + k ==>
                             ~(b <= page_base j /\ page_base (j + 1) <= b + words_at g' b * 8))))
      = if b = a then ()
        else begin
          assert (r > 0 /\ b == a + w * 8);
          FStar.Math.Lemmas.distributivity_add_left w r 8;
          assert (b + words_at g' b * 8 == e);
          let page (j: nat)
            : Lemma (~(b <= page_base j /\ page_base (j + 1) <= b + words_at g' b * 8))
            = FStar.Math.Lemmas.distributivity_add_left j 1 page_bytes
          in
          FStar.Classical.forall_intro page
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires blk)

/// Every page keeps its clauses.
let nr_pages (g: heap) (st: pstate) (i: nat{i < n_pages}) (k: pos) (wz: nat{wz < pow2 54})
  : Lemma (requires nr_ctx g st i k wz)
          (ensures (let g' = nr_heap g st i k wz in
                    let pm' = run_map st.pm i k in
                    map_ok pm' /\ LG.page_local_all g' pm' /\ tail_shape g'))
  = let g' = nr_heap g st i k wz in
    let pm' = run_map st.pm i k in
    nr_rest g st i k wz;
    pages_ok_elim g st;
    run_map_ok st.pm i k;
    run_entries st.pm i k;
    run_layout g i k wz (large_head st);
    nr_page g st i k wz;
    page_base_mono (i + k) n_pages;
    others_local g g' st.pm pm' i (i + k);
    LG.combine_run_pages g' pm' i;
    tail_kept g g' (i + k)

let nr_avail (g: heap) (st: pstate) (i: nat{i < n_pages}) (k: pos) (wz: nat)
  : Lemma (requires nr_ctx g st i k wz)
          (ensures avail_ok (run_state st i k (wz + 1)))
  = pages_ok_elim g st;
    run_entries st.pm i k;
    avail_frame st (run_state st i k (wz + 1))

/// The swept runs, before and after, for every address.
let nr_swept (g: heap) (st: pstate) (i: nat) (k: pos) (wz: nat)
  : Lemma (requires nr_ctx g st i k wz)
          (ensures forall (x: nat).
                     (in_swept_run st.pm x ==> in_swept_run (run_map st.pm i k) x) /\
                     (in_swept_run (run_map st.pm i k) x /\ (x < page_base i \/ x >= page_base (i + k)) ==>
                        in_swept_run st.pm x) /\
                     (page_base i <= x /\ x < page_base (i + k) ==>
                        in_swept_run (run_map st.pm i k) x /\ ~(in_swept_run st.pm x)))
  = pages_ok_elim g st;
    FStar.Classical.forall_intro (run_swept st.pm i k)

/// ---------------------------------------------------------------------------
/// The large lists after a new run
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec cells_unique (g: heap) (fp: U64.t) (cs1 cs2: list obj_addr)
  : Lemma (requires cells g fp cs1 /\ cells g fp cs2) (ensures cs1 == cs2) (decreases cs1)
  = match cs1, cs2 with
    | c1 :: t1, c2 :: t2 -> cells_unique g (read_word g (c1 <: hp_addr)) t1 t2
    | _ -> ()
#pop-options

/// A listed cell keeps its place: it lies in an old swept run.
let nr_old_cell (g: heap) (st: pstate) (i: nat{i < n_pages}) (k: pos) (wz: nat{wz < pow2 54})
                (cs: list obj_addr) (y: obj_addr)
  : Lemma (requires nr_ctx g st i k wz /\ lview g st cs /\ L.mem y cs)
          (ensures (let g' = nr_heap g st i k wz in
                    let st' = run_state st i k (wz + 1) in
                    Seq.mem y (objects zero_addr g') /\ U64.v (wosize_of_object y g') >= 1 /\
                    read_word g' (y <: hp_addr) == read_word g (y <: hp_addr) /\
                    is_blue y g' /\ large_listable g' st'.pm y /\
                    ~(page_base i <= U64.v y - 8 /\ U64.v y - 8 < page_base (i + k))))
  = let g' = nr_heap g st i k wz in
    nr_replaces g st i k wz;
    nr_swept g st i k wz;
    cells_mem g (large_head st) cs y;
    hd_address_spec y;
    LG.out_same g g' (page_base i) (page_base (i + k)) y;
    wosize_of_object_spec y g;
    wosize_of_object_spec y g'

/// A free listable block after the new run: the rest of the run, or an old
/// free listable block.
let nr_back (g: heap) (st: pstate) (i: nat{i < n_pages}) (k: pos) (wz: nat{wz < pow2 54}) (y: obj_addr)
  : Lemma (requires nr_ctx g st i k wz /\
                    (let g' = nr_heap g st i k wz in
                     Seq.mem y (objects zero_addr g') /\ is_blue y g' /\
                     large_listable g' (run_state st i k (wz + 1)).pm y))
          (ensures (U64.v y - 8 == page_base i + (wz + 1) * 8 /\ rest k (wz + 1) >= lg_min) \/
                   (Seq.mem y (objects zero_addr g) /\ is_blue y g /\ large_listable g st.pm y))
  = let g' = nr_heap g st i k wz in
    let a = page_base i in
    let e = page_base (i + k) in
    nr_rest g st i k wz;
    nr_replaces g st i k wz;
    nr_swept g st i k wz;
    run_layout g i k wz (large_head st);
    hd_address_spec y;
    if a <= U64.v y - 8 && U64.v y - 8 < e then begin
      replaces_frame_prefix g g' a e;
      LG.in_stretch g' a e y;
      hdr_obj g' y;
      is_blue_iff y g'
    end else
      LG.out_back g g' a e y

/// The rest of the run is short: it stays off the list.
let nr_large_short (g: heap) (st: pstate) (i: nat{i < n_pages}) (k: pos) (wz: nat{wz < pow2 54})
  : Lemma (requires nr_ctx g st i k wz /\ rest k (wz + 1) < lg_min)
          (ensures large_ok (nr_heap g st i k wz) (run_state st i k (wz + 1)))
  = let g' = nr_heap g st i k wz in
    let st' = run_state st i k (wz + 1) in
    let cs = walk g (large_head st) heap_words in
    pages_ok_elim g st;
    large_ok_lview g st;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (nr_old_cell g st i k wz cs));
    cells_frame g g' (large_head st) cs;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (nr_back g st i k wz));
    lview_large_ok g' st' cs

/// The address of the rest of the run, as a cell.
let rest_addr (i: nat) (k: pos) (wz: nat)
  : Lemma (requires i + k <= n_pages /\ rest k (wz + 1) >= lg_min)
          (ensures (let x = page_base i + (wz + 1) * 8 + 8 in
                    x + 8 <= page_base (i + k) /\ x < heap_size /\ x % 8 == 0 /\ x >= 8))
  = let a = page_base i in
    let w = wz + 1 in
    let r = rest k w in
    params_ok ();
    run_span i k;
    page_base_mono (i + k) n_pages;
    page_base_aligned i;
    aligned_plus_mul8 a (w + 1);
    FStar.Math.Lemmas.distributivity_add_left w r 8;
    FStar.Math.Lemmas.distributivity_add_left w 1 8

let rest_cell (i: nat) (k: pos) (wz: nat)
  : Pure obj_addr (requires i + k <= n_pages /\ rest k (wz + 1) >= lg_min)
                  (ensures fun y -> U64.v y == page_base i + (wz + 1) * 8 + 8)
  = rest_addr i k wz;
    U64.uint_to_t (page_base i + (wz + 1) * 8 + 8)

/// A free block right after an object the walk reaches is an object.
let rest_obj (g': heap) (a: nat) (w r: pos) (hd0: U64.t) (y: obj_addr)
  : Lemma (requires a % 8 == 0 /\ steps_to g' z a /\ words_at g' a == w /\
                    U64.v y == a + w * 8 + 8 /\ a + (w + r) * 8 <= heap_size /\ r >= 2 /\
                    words_at g' (a + w * 8) == r /\ color_at g' (a + w * 8) == Blue /\
                    read_word g' (mk_hp_addr (a + w * 8 + 8)) == hd0)
          (ensures Seq.mem y (objects zero_addr g') /\ U64.v (wosize_of_object y g') >= 1 /\
                   read_word g' (y <: hp_addr) == hd0 /\ is_blue y g' /\ whsize g' y == r)
  = FStar.Math.Lemmas.distributivity_add_left w r 8;
    hd_address_spec y;
    block_steps g' a w;
    steps_to_trans g' z a (a + w * 8);
    obj_iff g' y;
    hdr_obj g' y;
    is_blue_iff y g';
    assert (mk_hp_addr (a + w * 8 + 8) == (y <: hp_addr))

let rest_swept (g: heap) (st: pstate) (i: nat{i < n_pages}) (k: pos) (wz: nat) (x: nat)
  : Lemma (requires nr_ctx g st i k wz /\ page_base i <= x /\ x < page_base (i + k))
          (ensures in_swept_run (run_map st.pm i k) x /\ ~(in_swept_run st.pm x))
  = pages_ok_elim g st;
    run_swept st.pm i k x

/// The rest of the run, as a cell.
let nr_rest_cell (g: heap) (st: pstate) (i: nat{i < n_pages}) (k: pos) (wz: nat{wz < pow2 54})
  : Lemma (requires nr_ctx g st i k wz /\ rest k (wz + 1) >= lg_min)
          (ensures (let g' = nr_heap g st i k wz in
                    let st' = run_state st i k (wz + 1) in
                    let y = rest_cell i k wz in
                    LG.obj_at (page_base i + (wz + 1) * 8 + 8) == (y <: U64.t) /\
                    Seq.mem y (objects zero_addr g') /\ U64.v (wosize_of_object y g') >= 1 /\
                    read_word g' (y <: hp_addr) == large_head st /\
                    is_blue y g' /\ large_listable g' st'.pm y /\
                    ~(Seq.mem y (objects zero_addr g) /\ large_listable g st.pm y)))
  = nr_rest g st i k wz;
    let y = rest_cell i k wz in
    let g' = nr_heap g st i k wz in
    let a = page_base i in
    let e = page_base (i + k) in
    rest_addr i k wz;
    params_ok ();
    nr_replaces g st i k wz;
    replaces_frame_prefix g g' a e;
    run_layout g i k wz (large_head st);
    rest_obj g' a (wz + 1) (rest k (wz + 1)) (large_head st) y;
    hd_address_spec y;
    rest_swept g st i k wz (U64.v y - 8)

/// A list that leaves out an object of the heap has room for it.
let push_len (g: heap) (hd0: U64.t) (cs: list obj_addr) (y: obj_addr)
  : Lemma (requires cells g hd0 cs /\ L.noRepeats cs /\ L.length cs <= heap_words /\
                    ~(L.mem y cs) /\ Seq.mem y (objects zero_addr g))
          (ensures L.length cs <= heap_words - 1)
  = cells_valid g hd0 cs heap_words;
    Push.terminates_with_room g hd0 y;
    GC.Spec.Allocator.Lemmas.Common.fl_valid_weaken g hd0 heap_words (heap_words - 1);
    cells_of g hd0 (heap_words - 1);
    cells_unique g hd0 cs (walk g hd0 (heap_words - 1))

#push-options "--fuel 1"
let push_cells (g: heap) (y: obj_addr) (cs: list obj_addr) (hd0: U64.t)
  : Lemma (requires Seq.mem y (objects zero_addr g) /\ U64.v (wosize_of_object y g) >= 1 /\
                    read_word g (y <: hp_addr) == hd0 /\ cells g hd0 cs /\
                    ~(L.mem y cs) /\ L.noRepeats cs /\ L.length cs <= heap_words - 1)
          (ensures cells g (y <: U64.t) (y :: cs) /\ L.noRepeats (y :: cs) /\
                   L.length (y :: cs) <= heap_words /\
                   (forall (x: obj_addr). L.mem x (y :: cs) <==> (x == y \/ L.mem x cs)))
  = ()
#pop-options

let not_listed (g: heap) (st: pstate) (cs: list obj_addr) (y: obj_addr)
  : Lemma (requires lview g st cs /\ ~(Seq.mem y (objects zero_addr g) /\ large_listable g st.pm y))
          (ensures ~(L.mem y cs))
  = if L.mem y cs then cells_mem g (large_head st) cs y

let push_heads (st: pstate) (v: U64.t)
  : Lemma (requires Seq.length st.large == GC.Spec.SizeClass.n_lists)
          (ensures FLs.fls_head (FLs.fls_set st.large 0 v) 0 == v /\
                   Seq.length (FLs.fls_set st.large 0 v) == GC.Spec.SizeClass.n_lists /\
                   (forall (j: nat). 0 < j ==> FLs.fls_head (FLs.fls_set st.large 0 v) j == FLs.fls_head st.large j))
  = let aux (j: nat) : Lemma (FLs.fls_head (FLs.fls_set st.large 0 v) j ==
                              (if j = 0 then v else FLs.fls_head st.large j))
      = FLs.fls_head_set st.large 0 j v
    in
    FStar.Classical.forall_intro aux

let nr_large_push (g: heap) (st: pstate) (i: nat{i < n_pages}) (k: pos) (wz: nat{wz < pow2 54})
  : Lemma (requires nr_ctx g st i k wz /\ rest k (wz + 1) >= lg_min)
          (ensures large_ok (nr_heap g st i k wz) (run_state st i k (wz + 1)))
  = let g' = nr_heap g st i k wz in
    let st' = run_state st i k (wz + 1) in
    let cs = walk g (large_head st) heap_words in
    let hd0 = large_head st in
    pages_ok_elim g st;
    large_ok_lview g st;
    nr_rest_cell g st i k wz;
    let y = rest_cell i k wz in
    FStar.Classical.forall_intro (FStar.Classical.move_requires (nr_old_cell g st i k wz cs));
    cells_frame g g' hd0 cs;
    not_listed g st cs y;
    push_len g' hd0 cs y;
    push_cells g' y cs hd0;
    push_heads st (y <: U64.t);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (nr_back g st i k wz));
    lview_large_ok g' st' (y :: cs)

/// ---------------------------------------------------------------------------
/// The new run, assembled
/// ---------------------------------------------------------------------------

/// A fresh object at a free block's start.
let obj_core (g g': heap) (a: nat) (w: nat) (x: obj_addr)
  : Lemma (requires a % 8 == 0 /\ U64.v x == a + 8 /\ w >= 2 /\ a + w * 8 <= heap_size /\
                    steps_to g z a /\ color_at g a == Blue /\
                    steps_to g' z a /\ words_at g' a == w /\ color_at g' a == White)
          (ensures Seq.mem x (objects zero_addr g') /\
                   U64.v (wosize_of_object x g') == w - 1 /\
                   is_white x g' /\
                   ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)))
  = hd_address_spec x;
    obj_iff g' x;
    hdr_obj g' x;
    is_white_iff x g';
    LG.inside_free_blue g a x

let run_obj (i: nat) (k: pos) (wz: nat)
  : Pure obj_addr (requires i + k <= n_pages /\ i < n_pages /\ wz + 1 > small_max /\ rest k (wz + 1) >= 0)
                  (ensures fun x -> U64.v x == page_base i + 8 /\ page_base i + (wz + 1) * 8 <= heap_size)
  = params_ok ();
    cls_bounds 0;
    run_span i k;
    page_base_mono (i + k) n_pages;
    page_base_aligned i;
    FStar.Math.Lemmas.distributivity_add_left (wz + 1) (rest k (wz + 1)) 8;
    U64.uint_to_t (page_base i + 8)

let nr_object (g: heap) (st: pstate) (i: nat{i < n_pages}) (k: pos) (wz: nat{wz < pow2 54})
  : Lemma (requires nr_ctx g st i k wz)
          (ensures (let g' = nr_heap g st i k wz in
                    let obj = LG.obj_at (page_base i + 8) in
                    obj =!= 0UL /\ U64.v obj >= 8 /\ U64.v obj < heap_size /\ U64.v obj % 8 == 0 /\
                    (let x : obj_addr = obj in
                     Seq.mem x (objects zero_addr g') /\
                     U64.v (wosize_of_object x g') == wz /\
                     is_white x g' /\
                     ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)))))
  = nr_rest g st i k wz;
    let x = run_obj i k wz in
    let g' = nr_heap g st i k wz in
    let a = page_base i in
    let e = page_base (i + k) in
    page_base_aligned i;
    params_ok ();
    cls_bounds 0;
    nr_replaces g st i k wz;
    replaces_frame_prefix g g' a e;
    run_layout g i k wz (large_head st);
    pages_ok_elim g st;
    assert (page_local g st.pm i);
    obj_core g g' a (wz + 1) x

let nr_unswept (g: heap) (st: pstate) (i: nat{i < n_pages}) (k: pos) (wz: nat{wz < pow2 54})
  : Lemma (requires nr_ctx g st i k wz)
          (ensures unswept_unchanged g (nr_heap g st i k wz) st (run_state st i k (wz + 1)))
  = let g' = nr_heap g st i k wz in
    nr_rest g st i k wz;
    pages_ok_elim g st;
    run_entries st.pm i k;
    run_layout g i k wz (large_head st);
    let aux (j: nat{j < n_pages})
      : Lemma (not (entry st.pm j).swept ==>
               entry (run_map st.pm i k) j == entry st.pm j /\ page_kept g g' j)
      = if not (entry st.pm j).swept then begin
          assert (free_ok st.pm j);
          if j < i then page_base_mono (j + 1) i
          else page_base_mono (i + k) j
        end
    in
    FStar.Classical.forall_intro aux

/// **A new run is correct.**
let new_run_ok (g: heap) (st: pstate) (i: nat{i < n_pages}) (k: pos) (wz: nat{wz < pow2 54})
  : Lemma (requires nr_ctx g st i k wz)
          (ensures (let (g', st', obj) = new_run g st i k wz in alloc_ok g g' st st' wz obj))
  = let g' = nr_heap g st i k wz in
    let st' = run_state st i k (wz + 1) in
    pages_ok_elim g st;
    nr_replaces g st i k wz;
    replace_ok g g' (page_base i) (page_base (i + k));
    nr_pages g st i k wz;
    nr_avail g st i k wz;
    if rest k (wz + 1) >= lg_min then nr_large_push g st i k wz
    else nr_large_short g st i k wz;
    nr_object g st i k wz;
    nr_unswept g st i k wz;
    LG.alloc_ok_intro g g' st st' wz (LG.obj_at (page_base i + 8))
