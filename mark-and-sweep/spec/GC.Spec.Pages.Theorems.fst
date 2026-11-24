/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Theorems - what the page sweep and the allocator must prove
/// ---------------------------------------------------------------------------
///
/// The statements of docs/pages-allocator-proof-plan.md §2, as predicates on
/// a candidate function.  Stage 1 states them; stage 2 proves `alloc_meets`
/// of the allocator and stage 3 proves `sweep_page_meets` of the page sweep
/// and `sweep_run_meets` of the run sweep.
/// Stating them as predicates, rather than as lemmas without proofs, keeps
/// the tree free of admits.
///
/// Both are local by construction:
///   - the page sweep is given one page and may change only that page and
///     its page-map entry; the run sweep, only its run's words and its
///     pages' entries;
///   - the allocator's precondition is `pages_ok`, whose list clauses hold of
///     swept pages only, and it must leave every unswept page as it was.

module GC.Spec.Pages.Theorems

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

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module PI = GC.Spec.Pages.PoolInit

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// Only page `i`'s words changed.
let page_frame (g g': heap) (i: nat) : prop =
  forall (a: hp_addr). U64.v a + 8 <= page_base i \/ U64.v a >= page_base (i + 1) ==>
    read_word g' a == read_word g a

/// The block at `a` in `g'` is the block at `a` in `g`, made white: same
/// size, same tag, same fields.
let whitened (g g': heap) (a: hp_addr) : prop =
  read_word g' a == colorHeader (read_word g a) White /\
  (forall (b: hp_addr). U64.v a < U64.v b /\ U64.v b < U64.v a + words_at g (U64.v a) * 8 ==>
     read_word g' b == read_word g b)

/// ---------------------------------------------------------------------------
/// sweep_page_correct
/// ---------------------------------------------------------------------------

/// The words of slot `k` after its header are unchanged: a survivor's fields
/// and its filler.
let slot_rest_kept (g g': heap) (i: nat) (c: nat{c < n_cls}) (k: nat) : prop =
  forall (a: hp_addr). slot_base i c k < U64.v a /\ U64.v a < slot_base i c (k + 1) ==>
    read_word g' a == read_word g a

/// The page tail, a filler, is unchanged.
let pool_tail_kept (g g': heap) (i: nat) (c: nat{c < n_cls}) : prop =
  forall (a: hp_addr). slots_end i c <= U64.v a /\ U64.v a < page_base (i + 1) ==>
    read_word g' a == read_word g a

/// The page as the mark leaves it: its shape, and no grey block.
let marked_pool_page (g: heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls}) : prop =
  map_ok pm /\
  (entry pm i).kind == Pool c /\ not (entry pm i).swept /\
  pool_shape g i c /\
  (forall (k: nat). k < n_slots c /\ slot_used g i c k ==> color_at g (slot_base i c k) =!= Gray)

let sweep_page_ok (g: heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls})
                  (g': heap) (e: page_info) : prop =
  let pm' = Seq.upd pm i e in
  (* frame: one page, one entry *)
  page_frame g g' i /\
  e.swept == true /\
  (* survivors are kept, made white; the rest of their slot, the filler, stays *)
  (forall (k: nat{k < n_slots c}).
     slot_used g i c k /\ color_at g (slot_base i c k) == Black ==>
     slot_used g' i c k /\ whitened g g' (PI.slot_hd i c k) /\
     slot_rest_kept g g' i c k) /\
  (* everything else in the page is freed *)
  ((exists (k: nat). k < n_slots c /\ slot_used g i c k /\ color_at g (slot_base i c k) == Black) ==>
     e.kind == Pool c /\ pool_shape g' i c /\ pool_tail_kept g g' i c /\
     (forall (k: nat). k < n_slots c /\ ~(slot_used g i c k /\ color_at g (slot_base i c k) == Black) ==>
        slot_free g' i c k) /\
     pool_list_ok g' pm' i /\ pool_white g' pm' i) /\
  (* a page with no survivor goes back as a free page *)
  (~(exists (k: nat). k < n_slots c /\ slot_used g i c k /\ color_at g (slot_base i c k) == Black) ==>
     e.kind == Free /\ free_page_shape g' i)

/// `f` sweeps one pool page correctly.
let sweep_page_meets (f: heap -> page_map -> (i: nat{i < n_pages}) -> GTot (heap & page_info)) : prop =
  forall (g: heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls}).
    marked_pool_page g pm i c ==>
    (let (g', e) = f g pm i in sweep_page_ok g pm i c g' e)

/// ---------------------------------------------------------------------------
/// sweep_run_correct
/// ---------------------------------------------------------------------------

/// The block at `a` in `g'` is the block at `a` in `g`, made white, as
/// `whitened` but at a byte offset.
let whitened_at (g g': heap) (a: nat) : prop =
  a % 8 == 0 /\ a < heap_size /\
  hdr g' a == colorHeader (hdr g a) White /\
  (forall (b: hp_addr). a < U64.v b /\ U64.v b < a + words_at g a * 8 ==>
     read_word g' b == read_word g b)

/// A run as the mark leaves it: its shape, and no grey block.
let marked_run (g: heap) (pm: page_map) (h: nat{h < n_pages}) : prop =
  map_ok pm /\
  LargeHead? (entry pm h).kind /\ not (entry pm h).swept /\
  (let n = run_len (entry pm h).kind in
   run_shape g h n /\
   (forall (a: nat). run_block g h n a ==> color_at g a =!= Gray))

/// A stretch of the large list: from `fp`, through the cells `xs` in order,
/// to `tl`.  Each cell's first field links to the next.
let rec lchain (g: heap) (fp: U64.t) (xs: list obj_addr) (tl: U64.t) : Tot prop (decreases xs) =
  match xs with
  | [] -> fp == tl
  | x :: xs' -> fp == (x <: U64.t) /\ lchain g (read_word g (x <: hp_addr)) xs' tl

/// A survivor of the run: a black block of the walk over it.
let run_survivor (g: heap) (h: nat) (n: pos) (a: nat) : prop =
  run_block g h n a /\ color_at g a == Black

/// The pages of the swept run, `h .. h + n - 1`: each is swept, and is a free
/// page or a page of a run that lies inside them, with its shape and its
/// swept clause (L2, L6, L7).
let run_pages_ok (g': heap) (pm': page_map) (h: nat) (n: pos) : prop =
  forall (j: nat{j < n_pages}). h <= j /\ j < h + n ==>
    (entry pm' j).swept == true /\
    (match (entry pm' j).kind with
     | Free -> free_page_shape g' j
     | LargeHead m -> j + m <= h + n /\ run_shape g' j m /\ run_swept_ok g' pm' j
     | LargeCont -> (exists (u: nat{u < n_pages}). h <= u /\ u < j /\ in_run pm' u j)
     | Pool _ -> False)

let sweep_run_ok (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t)
                 (g': heap) (pm': page_map) (fp': U64.t) : prop =
  LargeHead? (entry pm h).kind /\
  (let n = run_len (entry pm h).kind in
   let s = page_base h in
   let e = page_base (h + n) in
   (* frame: the run's words and its pages' entries *)
   (forall (a: hp_addr). U64.v a < s \/ U64.v a >= e ==> read_word g' a == read_word g a) /\
   (forall (j: nat{j < n_pages}). j < h \/ j >= h + n ==> entry pm' j == entry pm j) /\
   map_ok pm' /\
   (* the run's pages: free pages and smaller swept runs *)
   run_pages_ok g' pm' h n /\
   steps_to g' s e /\
   (* survivors are kept, made white *)
   (forall (a: nat). run_survivor g h n a ==> steps_to g' s a /\ whitened_at g g' a) /\
   (* everything else is freed: a block that is not free was a survivor *)
   (forall (b: nat). steps_to g' s b /\ b < e /\ color_at g' b =!= Blue ==> run_survivor g h n b) /\
   (* a run with no survivor goes back as free pages *)
   (~(exists (a: nat). run_survivor g h n a) ==>
      (forall (j: nat{j < n_pages}). h <= j /\ j < h + n ==> (entry pm' j).kind == Free)) /\
   (* the free blocks of the new runs large enough to list, linked in front of `fp` *)
   (exists (xs: list obj_addr).
      lchain g' fp' xs fp /\ L.noRepeats xs /\
      (forall (y: obj_addr).
         L.mem y xs <==>
         (s <= U64.v y - 8 /\ U64.v y - 8 < e /\ steps_to g' s (U64.v y - 8) /\
          color_at g' (U64.v y - 8) == Blue /\ words_at g' (U64.v y - 8) >= lg_min /\
          in_swept_run pm' (U64.v y - 8)))))

/// `f` sweeps one large run correctly, linking the free blocks it lists in
/// front of the list head it is given.
let sweep_run_meets (f: heap -> page_map -> (h: nat{h < n_pages}) -> U64.t -> GTot (heap & page_map & U64.t)) : prop =
  forall (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t).
    marked_run g pm h ==>
    (let (g', pm', fp') = f g pm h fp in sweep_run_ok g pm h fp g' pm' fp')

/// ---------------------------------------------------------------------------
/// alloc_correct
/// ---------------------------------------------------------------------------

/// Every object that is not free keeps its place, header and fields.
let others_unchanged (g g': heap) : prop =
  forall (x: obj_addr).
    Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) ==>
    Seq.mem x (objects zero_addr g') /\
    read_word g' (hd_address x) == read_word g (hd_address x) /\
    (forall (b: hp_addr). U64.v x <= U64.v b /\ U64.v b < U64.v x + U64.v (wosize_of_object x g) * 8 ==>
       read_word g' b == read_word g b)

/// Page `i`'s words are unchanged.
let page_kept (g g': heap) (i: nat) : prop =
  forall (a: hp_addr). page_base i <= U64.v a /\ U64.v a < page_base (i + 1) ==>
    read_word g' a == read_word g a

/// Unswept pages, and their entries, are left as they were.
let unswept_unchanged (g g': heap) (st st': pstate) : prop =
  forall (i: nat{i < n_pages}).
    not (entry st.pm i).swept ==>
    entry st'.pm i == entry st.pm i /\ page_kept g g' i

/// The pages a large block of `w` words takes: `w` rounded up to pages.
let pages_for (w: pos) : pos = (w + page_wsize - 1) / page_wsize

/// Pages `i .. i + k - 1` are all free.
let free_run (pm: page_map) (i k: nat) : prop =
  i + k <= n_pages /\ (forall (j: nat). i <= j /\ j < i + k ==> (entry pm j).kind == Free)

/// No room for a block of `w` words: for a small block, no swept page of its
/// class has a free slot and no page is free; for a large one, no listed
/// block is large enough and no `pages_for w` consecutive pages are free.
let no_fit (g: heap) (st: pstate) (w: pos) : prop =
  (w <= small_max ==>
     (forall (p: nat{p < n_pages}). (entry st.pm p).kind =!= Free) /\
     (forall (p: nat{p < n_pages}). ~(has_free_slot st.pm (class_of w) p))) /\
  (w > small_max ==>
     (forall (y: obj_addr). Seq.mem y (objects zero_addr g) /\ is_blue y g /\
        large_listable g st.pm y ==> whsize g y < w) /\
     (forall (i: nat). ~(free_run st.pm i (pages_for w))))

/// A value the caller may store in a field: not a pointer, or a pointer that
/// resolves to an object of the heap that is not free.  The new object
/// itself is one.
let field_ok (g: heap) (v: U64.t) : prop =
  is_pointer v ==>
  Seq.mem (resolve_object (v <: obj_addr) g) (objects zero_addr g) /\
  infix_addr_wf g (objects zero_addr g) (v <: obj_addr) /\
  ~(is_blue (resolve_object (v <: obj_addr) g) g)

/// `g''` is `g'` with the fields of `x` written: every other word is kept,
/// and every field of `x` holds a value the caller may store.
let fields_written (g' g'': heap) (x: obj_addr) : prop =
  (forall (a: hp_addr).
     U64.v a < U64.v x \/ U64.v a >= U64.v x + U64.v (wosize_of_object x g') * 8 ==>
     read_word g'' a == read_word g' a) /\
  (forall (a: hp_addr).
     U64.v x <= U64.v a /\ U64.v a < U64.v x + U64.v (wosize_of_object x g') * 8 ==>
     field_ok g'' (read_word g'' a))

/// As OCaml's `caml_alloc_shr`, the allocator hands out the object with its
/// fields as they were, and the caller must write every field before the
/// heap is valid again.  So `alloc_ok` does not ask for `pages_ok` and
/// `well_formed_heap` of `g'` itself: it asks that they hold of every heap
/// the caller can make by writing valid values in the fields.
let alloc_ok (g g': heap) (st st': pstate) (wz: nat) (obj: U64.t) : prop =
  (obj == 0UL ==> g' == g /\ st' == st /\ (wz + 1 < pow2 54 ==> no_fit g st (wz + 1))) /\
  (obj =!= 0UL ==>
     U64.v obj >= 8 /\ U64.v obj < heap_size /\ U64.v obj % 8 == 0 /\
     (let x : obj_addr = obj in
      Seq.mem x (objects zero_addr g') /\
      U64.v (wosize_of_object x g') == wz /\
      is_white x g' /\
      ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
      (forall (g'': heap). fields_written g' g'' x ==>
         pages_ok g'' st' /\ well_formed_heap g'')) /\
     others_unchanged g g' /\
     unswept_unchanged g g' st st')

/// `f` allocates correctly.  Blocks of every size are allowed, including
/// wosize 0, which takes a 2-word slot.
let alloc_meets (f: heap -> pstate -> nat -> GTot (heap & pstate & U64.t)) : prop =
  forall (g: heap) (st: pstate) (wz: nat).
    pages_ok g st /\ well_formed_heap g ==>
    (let (g', st', obj) = f g st wz in alloc_ok g g' st st' wz obj)
