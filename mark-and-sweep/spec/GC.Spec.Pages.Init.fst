/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Init - vacuity: `pages_ok` holds of an empty heap
/// ---------------------------------------------------------------------------
///
/// The heap the runtime starts with: every page free (one blue block per
/// page), the heap's tail one blue block if it has room for a header, every
/// list empty.  `init_pages_ok` shows that this heap satisfies `pages_ok`,
/// for every heap size and both page sizes, so the invariant is not vacuous.

module GC.Spec.Pages.Init

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
module FLs = GC.Spec.FreeLists
module FL = GC.Spec.FreeList
module AL = GC.Spec.Allocator.Lemmas
module Chain = GC.Spec.Allocator.Lemmas.Chain
module Mark = GC.Spec.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// The header of a blue block of `w` words.
let blue_hdr (w: pos{w < pow2 20}) : U64.t =
  FStar.Math.Lemmas.pow2_lt_compat 54 20;
  FStar.Math.Lemmas.pow2_lt_compat 64 20;
  makeHeader (U64.uint_to_t (w - 1)) Blue 0UL

let blue_hdr_spec (w: pos{w < pow2 20})
  : Lemma (U64.v (getWosize (blue_hdr w)) + 1 == w /\ getColor (blue_hdr w) == Blue)
  = FStar.Math.Lemmas.pow2_lt_compat 54 20;
    FStar.Math.Lemmas.pow2_lt_compat 64 20;
    makeHeader_getWosize (U64.uint_to_t (w - 1)) Blue 0UL;
    makeHeader_getColor (U64.uint_to_t (w - 1)) Blue 0UL

/// The header of a free page, and of the heap's tail block.
let page_hdr : U64.t = cls_bounds 0; blue_hdr page_wsize

let page_addr (j: nat{j < n_pages}) : a: hp_addr{U64.v a == page_base j} =
  page_base_mono j (j + 1);
  page_base_aligned j;
  mk_hp_addr (page_base j)

/// ---------------------------------------------------------------------------
/// The heap
/// ---------------------------------------------------------------------------

let rec free_pages (g: heap) (k: nat{k <= n_pages}) : GTot heap (decreases k) =
  if k = 0 then g
  else (cls_bounds 0; write_word (free_pages g (k - 1)) (page_addr (k - 1)) (page_hdr))

let tail_w : nat = (heap_size - pages_end) / 8

let tail_hdr : U64.t = if tail_w < pow2 20 && tail_w > 0 then blue_hdr tail_w else 0UL

let tail_addr () : Pure hp_addr (requires heap_size - pages_end >= 16)
                                (ensures fun a -> U64.v a == pages_end) =
  pages_end_bound ();
  page_base_aligned n_pages;
  mk_hp_addr pages_end

let init_heap (g: heap) : GTot heap =
  let g1 = free_pages g n_pages in
  if heap_size - pages_end >= 16 then begin
    pages_end_bound ();
    cls_bounds 0;
    write_word g1 (tail_addr ()) tail_hdr
  end
  else g1

let init_state : pstate = {
  pm = all_free;
  avail = Seq.create n_cls 0UL;
  large = FLs.fls_empty;
}

/// ---------------------------------------------------------------------------
/// Reading it back
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec free_pages_page (g: heap) (k: nat{k <= n_pages}) (j: nat{j < k})
  : Lemma (ensures read_word (free_pages g k) (page_addr j) == page_hdr)
          (decreases k)
  = cls_bounds 0;
    if j = k - 1 then read_write_same (free_pages g (k - 1)) (page_addr j) (page_hdr)
    else begin
      free_pages_page g (k - 1) j;
      page_base_mono j (k - 1);
      read_write_different (free_pages g (k - 1)) (page_addr (k - 1)) (page_addr j)
        (page_hdr)
    end

/// A word at or above the end of the pages is not touched.
let rec free_pages_above (g: heap) (k: nat{k <= n_pages}) (a: hp_addr)
  : Lemma (requires U64.v a >= pages_end)
          (ensures read_word (free_pages g k) a == read_word g a)
          (decreases k)
  = if k = 0 then ()
    else begin
      cls_bounds 0;
      free_pages_above g (k - 1) a;
      page_base_mono (k - 1) n_pages;
      read_write_different (free_pages g (k - 1)) (page_addr (k - 1)) a (page_hdr)
    end
#pop-options

let init_page (g: heap) (j: nat{j < n_pages})
  : Lemma (read_word (init_heap g) (page_addr j) == page_hdr)
  = free_pages_page g n_pages j;
    if heap_size - pages_end >= 16 then begin
      page_base_mono j n_pages;
      cls_bounds 0;
      read_write_different (free_pages g n_pages) (tail_addr ()) (page_addr j) tail_hdr
    end

let init_tail (g: heap)
  : Lemma (requires heap_size - pages_end >= 16)
          (ensures read_word (init_heap g) (tail_addr ()) == tail_hdr)
  = pages_end_bound ();
    cls_bounds 0;
    read_write_same (free_pages g n_pages) (tail_addr ()) tail_hdr

/// ---------------------------------------------------------------------------
/// Its shape
/// ---------------------------------------------------------------------------

let init_free_page (g: heap) (j: nat{j < n_pages})
  : Lemma (free_page_shape (init_heap g) j)
  = init_page g j;
    cls_bounds 0;
    blue_hdr_spec page_wsize;
    page_base_mono j (j + 1);
    page_base_aligned j;
    assert (mk_hp_addr (page_base j) == page_addr j)

let tail_bound () : Lemma (heap_size - pages_end >= 16 ==> tail_w * 8 == heap_size - pages_end /\ tail_w < pow2 20)
  = pages_end_bound ();
    cls_bounds 0;
    page_base_aligned n_pages;
    assert (heap_size % 8 == 0);
    FStar.Math.Lemmas.lemma_mod_sub_distr heap_size pages_end 8;
    FStar.Math.Lemmas.lemma_div_exact (heap_size - pages_end) 8

let init_tail_shape (g: heap)
  : Lemma (tail_shape (init_heap g))
  = if heap_size - pages_end >= 16 then begin
      tail_bound ();
      init_tail g;
      blue_hdr_spec tail_w;
      pages_end_bound ();
      page_base_aligned n_pages;
      assert (mk_hp_addr pages_end == tail_addr ())
    end

let init_shape_ok (g: heap)
  : Lemma (shape_ok (init_heap g) all_free)
  = all_free_ok ();
    init_tail_shape g;
    let aux (i: nat{i < n_pages}) : Lemma (page_shape (init_heap g) all_free i)
      = init_free_page g i
    in
    FStar.Classical.forall_intro aux

/// ---------------------------------------------------------------------------
/// Every object of it is blue
/// ---------------------------------------------------------------------------

/// The walk over the empty heap lands only on page starts, or so close to
/// the end of the heap that no header fits.
let rec init_steps (g: heap) (j: nat{j <= n_pages}) (a: nat)
  : Lemma (requires steps_to (init_heap g) (page_base j) a)
          (ensures (exists (j': nat). j <= j' /\ j' <= n_pages /\ a == page_base j') \/
                   a + 8 >= heap_size)
          (decreases (n_pages - j))
  = let g' = init_heap g in
    steps_to_le g' (page_base j) a;
    if a = page_base j then ()
    else begin
      page_base_aligned j;
      page_base_mono j n_pages;
      pages_end_bound ();
      let s = mk_hp_addr (page_base j) in
      steps_to_next g' s a;
      if j < n_pages then begin
        init_free_page g j;
        assert (s == page_addr j);
        FStar.Math.Lemmas.distributivity_add_left j 1 page_bytes;
        init_steps g (j + 1) a
      end
      else if heap_size - pages_end >= 16 then begin
        tail_bound ();
        init_tail g;
        blue_hdr_spec tail_w;
        assert (s == tail_addr ());
        steps_to_le g' heap_size a
      end
      else ()
    end

let init_all_blue (g: heap) (x: obj_addr)
  : Lemma (requires Seq.mem x (objects zero_addr (init_heap g)))
          (ensures is_blue x (init_heap g))
  = let g' = init_heap g in
    objects_steps_to g' zero_addr x;
    hd_address_spec x;
    steps_to_refl g' (U64.v zero_addr);
    init_steps g 0 (U64.v (hd_address x));
    is_blue_iff x g';
    color_of_object_spec x g';
    let h = U64.v (hd_address x) in
    eliminate exists (j': nat). 0 <= j' /\ j' <= n_pages /\ h == page_base j'
    with begin
      if j' < n_pages then begin
        init_page g j';
        assert (hd_address x == page_addr j');
        cls_bounds 0;
        blue_hdr_spec page_wsize
      end else begin
        (* the tail block: it has room for a header, so it was written *)
        pages_end_bound ();
        page_base_aligned n_pages;
        assert (heap_size % 8 == 0);
        FStar.Math.Lemmas.lemma_mod_sub_distr heap_size pages_end 8;
        tail_bound ();
        init_tail g;
        assert (hd_address x == tail_addr ());
        blue_hdr_spec tail_w
      end
    end

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let init_large_ok (g: heap)
  : Lemma (large_ok (init_heap g) init_state)
  = let g' = init_heap g in
    let fls = FLs.fls_empty in
    let null (i: nat) (y: U64.t)
      : Lemma (FLs.fls_head fls i == 0UL /\ AL.chain_avoids g' 0UL y heap_words = true)
      = Chain.chain_avoids_null g' y heap_words
    in
    FStar.Classical.forall_intro_2 null;
    AL.fl_valid_null g' heap_words;
    FLs.fls_valid_intro g' fls;
    AL.fl_chain_terminates_terminal g' 0UL heap_words;
    FLs.fls_terminates_intro g' fls;
    let sound (i: nat) (y: U64.t) : Lemma (~(FL.reachable_on_fl g' (FLs.fls_head fls i) y))
      = introduce forall (n: nat). ~(FL.on_fl g' 0UL y n) with (if n = 0 then () else ())
    in
    FStar.Classical.forall_intro_2 sound;
    FStar.Classical.forall_intro (FLs.fls_avoids_iff g' fls)
#pop-options

#push-options "--fuel 1"
let init_avail_ok () : Lemma (avail_ok init_state)
  = let aux (c: nat{c < n_cls})
      : Lemma (exists (ps: list nat).
                 page_chain all_free (Seq.index init_state.avail c) ps /\ L.noRepeats ps /\
                 (forall (p: nat{p < n_pages}). L.mem p ps <==> has_free_slot all_free c p))
      = assert (page_chain all_free (Seq.index init_state.avail c) []);
        assert (L.noRepeats #nat [])
    in
    FStar.Classical.forall_intro aux
#pop-options

let init_page_clauses (g: heap) (i: nat{i < n_pages})
  : Lemma (pool_list_ok (init_heap g) all_free i /\ pool_white (init_heap g) all_free i /\
           run_swept_ok (init_heap g) all_free i)
  = assert (entry all_free i == free_entry)

let init_no_pointer_to_blue (g: heap)
  : Lemma (Mark.no_pointer_to_blue (init_heap g))
  = FStar.Classical.forall_intro (FStar.Classical.move_requires (init_all_blue g))

/// **Vacuity.**  The empty heap of pages satisfies the invariant.
let init_pages_ok (g: heap)
  : Lemma (pages_ok (init_heap g) init_state)
  = reveal_opaque (`%pages_ok) pages_ok;
    init_shape_ok g;
    init_large_ok g;
    init_avail_ok ();
    init_no_pointer_to_blue g;
    FStar.Classical.forall_intro (init_page_clauses g)
