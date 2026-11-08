/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Theorems - what the page sweep and the allocator must prove
/// ---------------------------------------------------------------------------
///
/// The statements of docs/pages-allocator-proof-plan.md §2, as predicates on
/// a candidate function.  Stage 1 states them; stage 2 proves `alloc_meets`
/// of the allocator and stage 3 proves `sweep_page_meets` of the page sweep.
/// Stating them as predicates, rather than as lemmas without proofs, keeps
/// the tree free of admits.
///
/// Both are local by construction:
///   - the page sweep is given one page and may change only that page and
///     its page-map entry;
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
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Seq = FStar.Seq
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
  (* survivors are kept, made white *)
  (forall (k: nat{k < n_slots c}).
     slot_used g i c k /\ color_at g (slot_base i c k) == Black ==>
     slot_used g' i c k /\ whitened g g' (PI.slot_hd i c k)) /\
  (* everything else in the page is freed *)
  ((exists (k: nat). k < n_slots c /\ slot_used g i c k /\ color_at g (slot_base i c k) == Black) ==>
     e.kind == Pool c /\ pool_shape g' i c /\
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

let alloc_ok (g g': heap) (st st': pstate) (wz: nat) (obj: U64.t) : prop =
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

/// `f` allocates correctly.  Blocks of every size are allowed, including
/// wosize 0, which takes a 2-word slot.
let alloc_meets (f: heap -> pstate -> nat -> GTot (heap & pstate & U64.t)) : prop =
  forall (g: heap) (st: pstate) (wz: nat).
    pages_ok g st /\ well_formed_heap g ==>
    (let (g', st', obj) = f g st wz in alloc_ok g g' st st' wz obj)
