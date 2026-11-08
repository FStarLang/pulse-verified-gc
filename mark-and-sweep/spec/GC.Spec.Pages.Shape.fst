/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Shape - the heap's contents, page by page
/// ---------------------------------------------------------------------------
///
/// What each kind of page holds, stated on the headers at fixed positions:
///   - a free page is one blue block covering it;
///   - in a pool page of class `c`, each slot is free (one blue block of
///     `cls c` words) or used (a non-blue block of at most `cls c` words at
///     the slot start, then one blue filler for the rest of the slot), and
///     the page tail, if any, is one blue filler;
///   - a large run is tiled by the walk from its first page to its end.
/// The heap's tail after the last page, if it has room for a header, is one
/// blue block.
///
/// `heap_tiled` is the main result: when every page has its shape, the global
/// walk `objects zero_addr g` reaches the end of the heap, and every page
/// start that begins a page's worth of blocks is an object of it.  So the
/// existing walk-based proofs (the mark, the minor collection) apply to a
/// heap of pages unchanged.

module GC.Spec.Pages.Shape

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Walk

module U64 = FStar.UInt64
module Seq = FStar.Seq
module WE = GC.Spec.WalkEnd

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Headers at an address
/// ---------------------------------------------------------------------------

/// The header word at `a`, or 0 where `a` cannot hold one.
let hdr (g: heap) (a: nat) : U64.t =
  if a < heap_size && a % 8 = 0 then read_word g (mk_hp_addr a) else 0UL

/// The block at `a` has `w` words, header included.
let words_at (g: heap) (a: nat) : pos = U64.v (getWosize (hdr g a)) + 1

let color_at (g: heap) (a: nat) : color_sem = getColor (hdr g a)

/// A blue block of `w` words at `a`.
let blue_block (g: heap) (a: nat) (w: pos) : prop =
  a % 8 == 0 /\ a < heap_size /\ words_at g a == w /\ color_at g a == Blue

/// ---------------------------------------------------------------------------
/// Pages
/// ---------------------------------------------------------------------------

let free_page_shape (g: heap) (i: nat) : prop =
  blue_block g (page_base i) page_wsize

/// A free slot: one blue block filling the slot.
let slot_free (g: heap) (i: nat) (c: nat{c < n_cls}) (k: nat) : prop =
  blue_block g (slot_base i c k) (cls c)

/// A used slot: a block that is not blue at the slot start, no larger than
/// the slot, and one blue filler for the rest.
let slot_used (g: heap) (i: nat) (c: nat{c < n_cls}) (k: nat) : prop =
  let a = slot_base i c k in
  a % 8 == 0 /\ a < heap_size /\
  color_at g a =!= Blue /\
  words_at g a <= cls c /\
  (words_at g a < cls c ==> blue_block g (a + words_at g a * 8) (cls c - words_at g a))

let slot_ok (g: heap) (i: nat) (c: nat{c < n_cls}) (k: nat) : prop =
  slot_free g i c k \/ slot_used g i c k

let pool_shape (g: heap) (i: nat) (c: nat{c < n_cls}) : prop =
  (forall (k: nat). k < n_slots c ==> slot_ok g i c k) /\
  (tail_words c > 0 ==> blue_block g (slots_end i c) (tail_words c))

let run_shape (g: heap) (i: nat) (n: pos) : prop =
  steps_to g (page_base i) (page_base (i + n))

let page_shape (g: heap) (pm: page_map) (i: nat{i < n_pages}) : prop =
  match (entry pm i).kind with
  | Free -> free_page_shape g i
  | Pool c -> pool_shape g i c
  | LargeHead n -> run_shape g i n
  | LargeCont -> True

/// The heap's tail: too short for a header, or one blue block.
let tail_shape (g: heap) : prop =
  heap_size - pages_end < 16 \/ blue_block g pages_end ((heap_size - pages_end) / 8)

/// L1–L3 and L6 of the plan, and the tail.
let shape_ok (g: heap) (pm: page_map) : prop =
  map_ok pm /\
  (forall (i: nat{i < n_pages}). page_shape g pm i) /\
  tail_shape g

/// ---------------------------------------------------------------------------
/// Each page is tiled
/// ---------------------------------------------------------------------------

/// A block of `w` words at `a` that ends inside the heap is one walk step.
let block_steps (g: heap) (a: nat) (w: pos)
  : Lemma (requires a % 8 == 0 /\ a < heap_size /\ words_at g a == w /\
                    a + w * 8 <= heap_size)
          (ensures steps_to g a (a + w * 8))
  = let ha = mk_hp_addr a in
    assert (hdr g a == read_word g ha);
    steps_to_one g ha (a + w * 8)

let free_page_steps (g: heap) (i: nat{i < n_pages})
  : Lemma (requires free_page_shape g i)
          (ensures steps_to g (page_base i) (page_base (i + 1)))
  = page_base_mono i (i + 1);
    FStar.Math.Lemmas.distributivity_add_left i 1 page_bytes;
    block_steps g (page_base i) page_wsize

#push-options "--z3rlimit 20"
let slot_steps (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (requires slot_ok g i c k)
          (ensures steps_to g (slot_base i c k) (slot_base i c (k + 1)))
  = let a = slot_base i c k in
    slot_base_succ i c k;
    slot_in_page i c k;
    slots_fill_page i c;
    page_base_mono (i + 1) n_pages;
    if words_at g a = cls c then block_steps g a (cls c)
    else begin
      let w = words_at g a in
      FStar.Math.Lemmas.distributivity_sub_left (cls c) w 8;
      block_steps g a w;
      block_steps g (a + w * 8) (cls c - w);
      steps_to_trans g a (a + w * 8) (a + cls c * 8)
    end
#pop-options

let rec slots_steps (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat)
  : Lemma (requires k <= n_slots c /\ (forall (j: nat). j < n_slots c ==> slot_ok g i c j))
          (ensures steps_to g (page_base i) (slot_base i c k))
          (decreases k)
  = if k = 0 then steps_to_refl g (page_base i)
    else begin
      slots_steps g i c (k - 1);
      slot_steps g i c (k - 1);
      steps_to_trans g (page_base i) (slot_base i c (k - 1)) (slot_base i c k)
    end

let pool_steps (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires pool_shape g i c)
          (ensures steps_to g (page_base i) (page_base (i + 1)))
  = slots_steps g i c (n_slots c);
    slots_fill_page i c;
    page_base_mono (i + 1) n_pages;
    if tail_words c > 0 then begin
      block_steps g (slots_end i c) (tail_words c);
      steps_to_trans g (page_base i) (slots_end i c) (page_base (i + 1))
    end

/// The walk from a walk page covers its span.
let page_steps (g: heap) (pm: page_map) (i: nat{i < n_pages})
  : Lemma (requires map_ok pm /\ walk_page pm i /\ page_shape g pm i)
          (ensures steps_to g (page_base i) (page_base (i + span pm i)))
  = match (entry pm i).kind with
    | Free -> free_page_steps g i
    | Pool c -> pool_steps g i c
    | LargeHead n -> ()
    | LargeCont -> ()

/// ---------------------------------------------------------------------------
/// The heap is tiled
/// ---------------------------------------------------------------------------

/// The walk from `zero_addr` reaches every walk page at or after `i`.
let rec reach_walk_pages (g: heap) (pm: page_map) (i: nat{i <= n_pages}) (j: nat{j <= n_pages})
  : Lemma (requires shape_ok g pm /\ walk_page pm i /\ walk_page pm j /\ i <= j /\
                    steps_to g (U64.v zero_addr) (page_base i))
          (ensures steps_to g (U64.v zero_addr) (page_base j))
          (decreases (n_pages - i))
  = if i = j then ()
    else begin
      next_walk_page pm i j;
      page_steps g pm i;
      let i' = i + span pm i in
      steps_to_trans g (U64.v zero_addr) (page_base i) (page_base i');
      reach_walk_pages g pm i' j
    end

let walk_pages_reached (g: heap) (pm: page_map) (j: nat{j <= n_pages})
  : Lemma (requires shape_ok g pm /\ walk_page pm j)
          (ensures steps_to g (U64.v zero_addr) (page_base j))
  = steps_to_refl g (U64.v zero_addr);
    if n_pages = 0 then ()
    else begin
      (* page 0 is a walk page: a continuation page has a run before it *)
      if (entry pm 0).kind = LargeCont then assert (cont_ok pm 0);
      reach_walk_pages g pm 0 j
    end

/// The first block of a walk lies inside it.
#push-options "--fuel 1 --ifuel 1"
let steps_to_first (g: heap) (a: hp_addr) (b: nat)
  : Lemma (requires steps_to g (U64.v a) b /\ U64.v a < b)
          (ensures U64.v a + block_bytes g a <= b)
  = assert (mk_hp_addr (U64.v a) == a)
#pop-options

/// **The heap of pages is tiled.**  The global walk reaches the end of the
/// heap, and every walk page with room for a header starts an object.
let heap_tiled (g: heap) (pm: page_map)
  : Lemma (requires shape_ok g pm)
          (ensures WE.walk_end g zero_addr + 8 >= heap_size /\
                   (forall (j: nat{j < n_pages}).
                      walk_page pm j /\ page_base j + 8 < heap_size ==>
                      page_base j % 8 == 0 /\
                      Seq.mem (f_address (mk_hp_addr (page_base j))) (objects zero_addr g)))
  = pages_end_bound ();
    page_base_aligned n_pages;
    walk_pages_reached g pm n_pages;
    if heap_size - pages_end < 16 then
      steps_to_walk_end g zero_addr pages_end
    else begin
      let w = (heap_size - pages_end) / 8 in
      assert (heap_size % 8 == 0);
      FStar.Math.Lemmas.lemma_mod_sub_distr heap_size pages_end 8;
      FStar.Math.Lemmas.lemma_div_exact (heap_size - pages_end) 8;
      block_steps g pages_end w;
      steps_to_trans g (U64.v zero_addr) pages_end heap_size;
      steps_to_walk_end g zero_addr heap_size
    end;
    let at (j: nat{j < n_pages})
      : Lemma (walk_page pm j /\ page_base j + 8 < heap_size ==>
               page_base j % 8 == 0 /\
               Seq.mem (f_address (mk_hp_addr (page_base j))) (objects zero_addr g))
      = if walk_page pm j && page_base j + 8 < heap_size then begin
          page_base_aligned j;
          page_base_mono j (j + span pm j);
          next_walk_page pm j j;
          walk_pages_reached g pm j;
          page_steps g pm j;
          let a = mk_hp_addr (page_base j) in
          steps_to_first g a (page_base (j + span pm j));
          steps_to_objects g zero_addr a (page_base j + block_bytes g a)
        end
    in
    FStar.Classical.forall_intro at
