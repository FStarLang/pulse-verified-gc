/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Inv - the invariant of the page allocator, `pages_ok`
/// ---------------------------------------------------------------------------
///
/// `pages_ok g st` links the heap `g` to the allocator state `st`: the page
/// map, the lists of pages with a free slot, and the large-object lists.
/// Its clauses are numbered as in docs/pages-allocator-proof-plan.md §1.4:
///
///   L1–L3, L6  `shape_ok` (GC.Spec.Pages.Shape): the heap is tiled page by
///              page, so the global walk reaches the end of the heap;
///   L4  a swept pool page's free-slot list holds exactly its free slots;
///   L5  a swept pool page holds no black or grey block;
///   L7  a swept run holds no black or grey block, no two adjacent blue
///       blocks, and no page wholly inside one blue block;
///   L8  the list of class `c` holds exactly the swept pages of class `c`
///       with a free slot;
///   L9  the large lists are #46's lists, restricted to swept runs and to
///       blocks of at least `lg_min` words, and every such free block is on
///       them;
///   L10 no object points to a free block (`GC.Spec.Mark.no_pointer_to_blue`).
///
/// L4, L5, L7 and L8 constrain swept pages only.  Unswept pages are held to
/// their shape alone, which is what lets the allocator and a later
/// incremental sweep work while some pages are unswept.

module GC.Spec.Pages.Inv

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

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module FLs = GC.Spec.FreeLists
module FL = GC.Spec.FreeList
module Mark = GC.Spec.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The allocator state, as the specification sees it
/// ---------------------------------------------------------------------------

noeq type pstate = {
  pm: page_map;
  avail: Seq.seq U64.t;       (* per class: the first page with a free slot, as index + 1; 0 = none *)
  large: FLs.fl_state;        (* #46's lists, for the large-object area *)
}

/// The smallest free block the large lists hold: one word more than the
/// largest small block, so any listed block can serve a large request.
let lg_min : pos = small_max + 1

/// ---------------------------------------------------------------------------
/// L4: the free-slot list of a pool page
/// ---------------------------------------------------------------------------

/// A free slot's list entry is its object address, one word past the slot
/// start; its first field links to the next entry, 0 ending the list.
let slot_obj (i: nat) (c: nat{c < n_cls}) (k: nat) : nat = slot_base i c k + 8

#push-options "--fuel 1"
let rec slot_chain (g: heap) (i: nat) (c: nat{c < n_cls}) (hd: U64.t) (ks: list nat)
  : Tot prop (decreases ks)
  = match ks with
    | [] -> hd == 0UL
    | k :: ks' ->
      k < n_slots c /\ U64.v hd == slot_obj i c k /\ slot_free g i c k /\
      slot_chain g i c (hdr g (slot_obj i c k)) ks'
#pop-options

let pool_list_ok (g: heap) (pm: page_map) (i: nat{i < n_pages}) : prop =
  match (entry pm i).kind with
  | Pool c ->
    (entry pm i).swept ==>
    (exists (ks: list nat).
       slot_chain g i c (entry pm i).free_head ks /\
       L.noRepeats ks /\
       (forall (k: nat). k < n_slots c ==> (L.mem k ks <==> slot_free g i c k)) /\
       (entry pm i).nfree == L.length ks)
  | _ -> True

/// ---------------------------------------------------------------------------
/// L5: a swept pool page holds white blocks only
/// ---------------------------------------------------------------------------

let pool_white (g: heap) (pm: page_map) (i: nat{i < n_pages}) : prop =
  match (entry pm i).kind with
  | Pool c ->
    (entry pm i).swept ==>
    (forall (k: nat). k < n_slots c /\ slot_used g i c k ==> color_at g (slot_base i c k) == White)
  | _ -> True

/// ---------------------------------------------------------------------------
/// L7: a swept large run
/// ---------------------------------------------------------------------------

/// `a` is a block of the run of `n` pages that starts at page `h`.
let run_block (g: heap) (h: nat) (n: pos) (a: nat) : prop =
  steps_to g (page_base h) a /\ a < page_base (h + n)

let run_swept_ok (g: heap) (pm: page_map) (h: nat{h < n_pages}) : prop =
  match (entry pm h).kind with
  | LargeHead n ->
    (entry pm h).swept ==>
    (forall (a: nat). run_block g h n a ==>
       (* white or blue *)
       (color_at g a == White \/ color_at g a == Blue) /\
       (* no two adjacent blue blocks *)
       (color_at g a == Blue /\ a + words_at g a * 8 < page_base (h + n) ==>
          color_at g (a + words_at g a * 8) =!= Blue) /\
       (* whole free pages are given back *)
       (color_at g a == Blue ==>
          (forall (j: nat). h <= j /\ j < h + n ==>
             ~(a <= page_base j /\ page_base (j + 1) <= a + words_at g a * 8))))
  | _ -> True

/// ---------------------------------------------------------------------------
/// L8: the lists of pages with a free slot
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec page_chain (pm: page_map) (hd: U64.t) (ps: list nat) : Tot prop (decreases ps) =
  match ps with
  | [] -> hd == 0UL
  | p :: ps' -> p < n_pages /\ U64.v hd == p + 1 /\ page_chain pm (entry pm p).next ps'
#pop-options

let has_free_slot (pm: page_map) (c: nat{c < n_cls}) (p: nat{p < n_pages}) : bool =
  (entry pm p).kind = Pool c && (entry pm p).swept && (entry pm p).nfree > 0

let avail_ok (st: pstate) : prop =
  Seq.length st.avail == n_cls /\
  (forall (c: nat{c < n_cls}).
     exists (ps: list nat).
       page_chain st.pm (Seq.index st.avail c) ps /\ L.noRepeats ps /\
       (forall (p: nat{p < n_pages}). L.mem p ps <==> has_free_slot st.pm c p))

/// ---------------------------------------------------------------------------
/// L9: the large lists
/// ---------------------------------------------------------------------------

/// `a` lies in a swept run.
let in_swept_run (pm: page_map) (a: nat) : prop =
  exists (h: nat{h < n_pages}).
    LargeHead? (entry pm h).kind /\ (entry pm h).swept /\
    page_base h <= a /\ a < page_base (h + run_len (entry pm h).kind)

/// A block the large lists may hold: in a swept run, of at least `lg_min`
/// words.
let large_listable (g: heap) (pm: page_map) (y: obj_addr) : prop =
  in_swept_run pm (U64.v (hd_address y)) /\ whsize g y >= lg_min

let large_ok (g: heap) (st: pstate) : prop =
  FLs.fls_valid g st.large /\
  FLs.fls_terminates g st.large /\
  (* every listed block is listable *)
  (forall (y: obj_addr). Seq.mem y (objects zero_addr g) /\ ~(large_listable g st.pm y) ==>
     FLs.fls_avoids g st.large (y <: U64.t)) /\
  (* every listable free block is listed *)
  (forall (y: obj_addr). Seq.mem y (objects zero_addr g) /\ is_blue y g /\ large_listable g st.pm y ==>
     FL.reachable_on_fl g (FLs.fls_head st.large
                             (GC.Spec.SizeClass.size_class (U64.v (wosize_of_object y g)))) y)

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

let pages_ok (g: heap) (st: pstate) : prop =
  shape_ok g st.pm /\
  (forall (i: nat{i < n_pages}).
     pool_list_ok g st.pm i /\ pool_white g st.pm i /\ run_swept_ok g st.pm i) /\
  avail_ok st /\
  large_ok g st /\
  Mark.no_pointer_to_blue g

/// The walk facts every client needs, from `pages_ok` alone.
let pages_ok_tiled (g: heap) (st: pstate)
  : Lemma (requires pages_ok g st)
          (ensures GC.Spec.WalkEnd.walk_end g zero_addr + 8 >= heap_size)
  = heap_tiled g st.pm
