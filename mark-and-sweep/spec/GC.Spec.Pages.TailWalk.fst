/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.TailWalk - the walk of a heap of pages ends at `heap_size`
/// ---------------------------------------------------------------------------
///
/// Plan §23.5 (L1).  The pages leave at least two words at the end of the
/// heap (`GC.Spec.Pages.Layout.n_pages`), and the heap's tail is one blue
/// block (`tail_shape`, its long case).  So in every state whose pages are
/// tiled (`shape_ok`) the walk steps from the end of the pages over the tail
/// block to `heap_size` exactly: a page tail of one word is never the heap's
/// last word, and the walk's end does not move when a page changes kind.
///
/// `shape_walk_end` is the lemma; `steps_reaches` restates the page walk
/// (`GC.Spec.Pages.Walk.steps_to`) as `GC.Spec.Walk.reaches` below the end
/// of the heap.

module GC.Spec.Pages.TailWalk

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
module W = GC.Spec.Walk

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// The page walk below the end of the heap is the walk of `GC.Spec.Walk`.
let rec steps_reaches (g: heap) (a: hp_addr) (b: nat)
  : Lemma (requires steps_to g (U64.v a) b /\ b < heap_size)
          (ensures W.reaches g a b)
          (decreases (b - U64.v a))
  = steps_to_le g (U64.v a) b;
    if U64.v a = b then W.reaches_refl g a
    else begin
      steps_to_next g a b;
      let n = U64.v a + block_bytes g a in
      assert (n == W.bnext g a);
      W.bnext_facts g a;
      W.reaches_step g a;
      if n = b then ()
      else begin
        steps_to_le g n b;
        let na = mk_hp_addr n in
        steps_reaches g na b;
        W.reaches_trans g a na b
      end
    end

/// The heap's tail: at least two words, after the last page.
let tail_room ()
  : Lemma (pages_end + 16 <= heap_size /\ pages_end % 8 == 0 /\
           (heap_size - pages_end) % 8 == 0 /\
           ((heap_size - pages_end) / 8) * 8 == heap_size - pages_end)
  = pages_end_bound ();
    page_base_aligned n_pages;
    assert (heap_size % 8 == 0);
    FStar.Math.Lemmas.lemma_mod_sub_distr heap_size pages_end 8;
    FStar.Math.Lemmas.lemma_div_exact (heap_size - pages_end) 8

/// **The walk of a heap of pages ends at the end of the heap**, and the
/// heap is dense.
let shape_walk_end (g: heap) (pm: page_map)
  : Lemma (requires shape_ok g pm)
          (ensures W.reaches g zero_addr heap_size /\ W.walk_end g zero_addr == heap_size /\
                   heap_objects_dense g /\ Seq.length (objects zero_addr g) > 0)
  = tail_room ();
    walk_pages_reached g pm n_pages;
    steps_reaches g zero_addr pages_end;
    let pe = mk_hp_addr pages_end in
    let w = (heap_size - pages_end) / 8 in
    assert (tail_shape g);
    assert (blue_block g pages_end w);
    assert (hdr g pages_end == read_word g pe);
    assert (W.bnext g pe == heap_size);
    assert (W.can_step g pe);
    W.reaches_snoc g zero_addr pe;
    W.walk_end_of_reaches g zero_addr heap_size;
    W.reaches_unfold g zero_addr heap_size;
    W.dense_of_reaches_end g heap_size

/// **The heap's tail is a free object of the walk**, over the heap's last
/// word: its header at the end of the pages, its block to `heap_size`.
#push-options "--z3rlimit 30"
let tail_object (g: heap) (pm: page_map)
  : Lemma (requires shape_ok g pm)
          (ensures pages_end + 16 <= heap_size /\
                   (let t : obj_addr = mk_hp_addr (pages_end + 8) in
                    Seq.mem t (objects zero_addr g) /\ is_blue t g /\
                    GC.Spec.FusedSweep.Lossless.in_extent g t (heap_size - 8)))
  = tail_room ();
    walk_pages_reached g pm n_pages;
    steps_reaches g zero_addr pages_end;
    let pe = mk_hp_addr pages_end in
    let w = (heap_size - pages_end) / 8 in
    let t : obj_addr = mk_hp_addr (pages_end + 8) in
    assert (tail_shape g);
    assert (blue_block g pages_end w);
    assert (hdr g pages_end == read_word g pe);
    assert (W.can_step g pe);
    hd_address_spec t;
    assert (hd_address t == pe);
    W.objects_mem_iff g zero_addr t;
    is_blue_iff t g;
    color_of_object_spec t g;
    wosize_of_object_spec t g
#pop-options
