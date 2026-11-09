/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.SweepVacuity - the sweep theorems are not vacuous
/// ---------------------------------------------------------------------------
///
/// `sweep_page_correct` and `sweep_run_correct` assume a page or run as the
/// mark leaves it.  Here, for any page of the heap:
///   - a fresh pool page whose first slot holds a black block is a marked
///     pool page; the sweep keeps it a pool page, the slot used and white;
///   - the same page with no black block is a marked pool page too; the
///     sweep gives it back as a free page;
///   - a run of one page holding one black block is a marked run; the sweep
///     keeps the block, made white;
///   - the same run holding one white block is a marked run; the sweep gives
///     its page back as a free page.
/// So both preconditions hold, and both outcomes of each sweep occur.
///
/// The whole sweep's precondition (`SweepAll.sweep_ready` and `mark_done`)
/// holds of the empty heap of pages (`sweep_all_ready`).

module GC.Spec.Pages.SweepVacuity

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
open GC.Spec.Pages.Init
open GC.Spec.Pages.PoolInit
open GC.Spec.Pages.Theorems

module U64 = FStar.UInt64
module Seq = FStar.Seq
module SP = GC.Spec.Pages.SweepPage
module SR = GC.Spec.Pages.SweepRun
module B = GC.Spec.Pages.Blocks
module SA = GC.Spec.Pages.SweepAll
module Mark = GC.Spec.Mark

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// A header of `w` words, of colour `col`.
let hdr_of (w: pos{w < pow2 20}) (col: color) : U64.t =
  FStar.Math.Lemmas.pow2_lt_compat 54 20;
  FStar.Math.Lemmas.pow2_lt_compat 64 20;
  makeHeader (U64.uint_to_t (w - 1)) col 0UL

let hdr_of_spec (w: pos{w < pow2 20}) (col: color)
  : Lemma (U64.v (getWosize (hdr_of w col)) + 1 == w /\ getColor (hdr_of w col) == col)
  = FStar.Math.Lemmas.pow2_lt_compat 54 20;
    FStar.Math.Lemmas.pow2_lt_compat 64 20;
    makeHeader_getWosize (U64.uint_to_t (w - 1)) col 0UL;
    makeHeader_getColor (U64.uint_to_t (w - 1)) col 0UL

/// ---------------------------------------------------------------------------
/// A pool page
/// ---------------------------------------------------------------------------

/// Every page free but page `i`, an unswept pool page of class `c`.
let pool_map (i: nat{i < n_pages}) (c: nat{c < n_cls}) : page_map =
  Seq.upd all_free i { free_entry with kind = Pool c; swept = false }

let pool_map_ok (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (map_ok (pool_map i c) /\ (entry (pool_map i c) i).kind == Pool c /\
           not (entry (pool_map i c) i).swept)
  = let pm = pool_map i c in
    let aux (j: nat{j < n_pages}) : Lemma (run_ok pm j /\ cont_ok pm j /\ free_ok pm j)
      = if j <> i then assert (entry pm j == free_entry)
    in
    FStar.Classical.forall_intro aux

/// A fresh pool page whose first slot holds a black block filling it.
let pool_live (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) : GTot heap =
  cls_bounds c;
  write_word (pool_init g i c) (slot_hd i c 0) (hdr_of (cls c) Black)

/// Slots after the first are untouched by the write.
let pool_live_other (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (requires k > 0)
          (ensures slot_free (pool_live g i c) i c k)
  = cls_bounds c;
    let g0 = pool_init g i c in
    pool_init_free g i c k;
    slot_fits i c k;
    slot_below i c 0 k;
    let a = slot_hd i c k in
    read_write_different g0 (slot_hd i c 0) a (hdr_of (cls c) Black);
    assert (mk_hp_addr (slot_base i c k) == a)

let pool_live_marked (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (marked_pool_page (pool_live g i c) (pool_map i c) i c /\
           slot_used (pool_live g i c) i c 0 /\
           color_at (pool_live g i c) (slot_base i c 0) == Black)
  = cls_bounds c;
    let g0 = pool_init g i c in
    let g1 = pool_live g i c in
    pool_map_ok i c;
    pool_init_shape g i c;
    slot_fits i c 0;
    read_write_same g0 (slot_hd i c 0) (hdr_of (cls c) Black);
    hdr_of_spec (cls c) Black;
    assert (mk_hp_addr (slot_base i c 0) == slot_hd i c 0);
    assert (slot_used g1 i c 0);
    let slots (k: nat) : Lemma (k < n_slots c ==> slot_ok g1 i c k /\
                                 (slot_used g1 i c k ==> color_at g1 (slot_base i c k) =!= Gray))
      = if k < n_slots c && k > 0 then pool_live_other g i c k
    in
    FStar.Classical.forall_intro slots;
    if tail_words c > 0 then begin
      slots_fill_page i c;
      slot_below i c 0 (n_slots c);
      page_base_mono (i + 1) n_pages;
      slot_base_aligned i c (n_slots c);
      read_write_different g0 (slot_hd i c 0) (mk_hp_addr (slots_end i c)) (hdr_of (cls c) Black)
    end

/// **A page with a survivor stays a pool page, the survivor made white.**
let sweep_page_keeps (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (let (g', e) = SP.sweep_page (pool_live g i c) (pool_map i c) i in
           e.kind == Pool c /\ slot_used g' i c 0 /\
           color_at g' (slot_base i c 0) == White)
  = cls_bounds c;
    pool_live_marked g i c;
    SP.sweep_page_correct ();
    let g1 = pool_live g i c in
    let (g', e) = SP.sweep_page g1 (pool_map i c) i in
    assert (sweep_page_ok g1 (pool_map i c) i c g' e);
    hdr_of_spec (cls c) Black;
    colorHeader_getColor (read_word g1 (slot_hd i c 0)) White;
    slot_fits i c 0;
    assert (mk_hp_addr (slot_base i c 0) == slot_hd i c 0)

/// **A fresh pool page is marked, and is given back as a free page.**
let sweep_page_frees (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (marked_pool_page (pool_init g i c) (pool_map i c) i c /\
           (let (g', e) = SP.sweep_page (pool_init g i c) (pool_map i c) i in
            e.kind == Free /\ free_page_shape g' i))
  = pool_map_ok i c;
    pool_init_shape g i c;
    let g0 = pool_init g i c in
    let free (k: nat) : Lemma (k < n_slots c ==> slot_free g0 i c k /\ ~(slot_used g0 i c k))
      = if k < n_slots c then pool_init_free g i c k
    in
    FStar.Classical.forall_intro free;
    SP.sweep_page_correct ()

/// ---------------------------------------------------------------------------
/// A large run
/// ---------------------------------------------------------------------------

/// Every page free but page `i`, an unswept run of one page.
let run_map (i: nat{i < n_pages}) : page_map =
  Seq.upd all_free i { free_entry with kind = LargeHead 1; swept = false }

let run_map_ok (i: nat{i < n_pages})
  : Lemma (map_ok (run_map i) /\ (entry (run_map i) i).kind == LargeHead 1 /\
           not (entry (run_map i) i).swept)
  = let pm = run_map i in
    let aux (j: nat{j < n_pages}) : Lemma (run_ok pm j /\ cont_ok pm j /\ free_ok pm j)
      = if j <> i then assert (entry pm j == free_entry)
    in
    FStar.Classical.forall_intro aux

/// One block of colour `col` filling page `i`.
let run_heap (g: heap) (i: nat{i < n_pages}) (col: color) : GTot heap =
  cls_bounds 0;
  write_word g (page_addr i) (hdr_of page_wsize col)

let run_heap_marked (g: heap) (i: nat{i < n_pages}) (col: color)
  : Lemma (requires col =!= Gray)
          (ensures marked_run (run_heap g i col) (run_map i) i /\
                   run_block (run_heap g i col) i 1 (page_base i) /\
                   color_at (run_heap g i col) (page_base i) == col /\
                   (forall (a: nat). run_block (run_heap g i col) i 1 a ==> a == page_base i))
  = cls_bounds 0;
    let g1 = run_heap g i col in
    run_map_ok i;
    read_write_same g (page_addr i) (hdr_of page_wsize col);
    hdr_of_spec page_wsize col;
    page_base_mono i (i + 1);
    page_base_mono (i + 1) n_pages;
    FStar.Math.Lemmas.distributivity_add_left i 1 page_bytes;
    block_steps g1 (page_base i) page_wsize;
    steps_to_refl g1 (page_base i);
    let one (a: nat) : Lemma (run_block g1 i 1 a ==> a == page_base i)
      = if run_block g1 i 1 a then B.one_block_pos g1 (page_base i) a
    in
    FStar.Classical.forall_intro one

/// **A run with a survivor keeps it, made white.**
let sweep_run_keeps (g: heap) (i: nat{i < n_pages}) (fp: U64.t)
  : Lemma (let (g', pm', fp') = SR.sweep_run (run_heap g i Black) (run_map i) i fp in
           run_survivor (run_heap g i Black) i 1 (page_base i) /\
           steps_to g' (page_base i) (page_base i) /\
           whitened_at (run_heap g i Black) g' (page_base i))
  = run_heap_marked g i Black;
    SR.sweep_run_correct ()

/// **A run with no survivor gives its page back.**
let sweep_run_frees (g: heap) (i: nat{i < n_pages}) (fp: U64.t)
  : Lemma (marked_run (run_heap g i White) (run_map i) i /\
           (let (g', pm', fp') = SR.sweep_run (run_heap g i White) (run_map i) i fp in
            (entry pm' i).kind == Free /\ free_page_shape g' i))
  = run_heap_marked g i White;
    SR.sweep_run_correct ();
    let g1 = run_heap g i White in
    let (g', pm', fp') = SR.sweep_run g1 (run_map i) i fp in
    assert (sweep_run_ok g1 (run_map i) i fp g' pm' fp');
    assert (~(exists (a: nat). run_survivor g1 i 1 a))

/// ---------------------------------------------------------------------------
/// The whole sweep
/// ---------------------------------------------------------------------------

/// **The whole sweep's precondition holds** of the empty heap of pages.
let sweep_all_ready (g: heap)
  : Lemma (SA.sweep_ready (init_heap g) init_state /\ SA.mark_done (init_heap g))
  = let g' = init_heap g in
    GC.Spec.Pages.Alloc.init_alloc_pre g;
    GC.Spec.Pages.Step.pages_ok_elim g' init_state;
    let blue (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr g') ==> ~(is_black x g') /\ not (is_gray x g'))
      = if Seq.mem x (objects zero_addr g') then begin
          init_all_blue g x;
          Mark.colors_exclusive x g'
        end
    in
    FStar.Classical.forall_intro blue;
    let kinds (j: nat{j < n_pages}) : Lemma (entry init_state.pm j == free_entry)
      = ()
    in
    FStar.Classical.forall_intro kinds
