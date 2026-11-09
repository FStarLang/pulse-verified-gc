/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.SweepTags - the free blocks the sweep leaves are not infix
/// ---------------------------------------------------------------------------
///
/// `well_formed_heap` asks that no object of the heap be infix, free blocks
/// included.  The sweep theorems say which blocks are free but not their
/// tags.  `blue_ok g0 g i k` says that every free block of the unit of `k`
/// pages at page `i`, swept from `g0` to `g`, either has a header the sweep
/// wrote, of tag 0, or is a block of `g0` there with its header kept:
///   - a freed slot, a freed page and a merged block of a run get a new blue
///     header of tag 0 (`pool_blue_ok`, `run_blue_ok`);
///   - a survivor's filler, a pool page's tail and an untouched free page
///     are blocks of `g0`, kept.
/// `GC.Spec.Pages.SweepWf` carries these facts through the whole sweep.

module GC.Spec.Pages.SweepTags

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
open GC.Spec.Pages.Theorems
open GC.Spec.Pages.Blk

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module R = GC.Spec.Pages.Replace
module B = GC.Spec.Pages.Blocks
module FR = GC.Spec.Pages.Frame
module PI = GC.Spec.Pages.PoolInit
module Init = GC.Spec.Pages.Init
module Pool = GC.Spec.Pages.Pool
module SP = GC.Spec.Pages.SweepPage
module SR = GC.Spec.Pages.SweepRun
module SU = GC.Spec.Pages.SweepUnits
module MP = GC.Spec.Pages.MarkPhase

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let blue_ok (g0 g: heap) (i k: nat) : prop =
  forall (b: nat).
    steps_to g (page_base i) b /\ b < page_base (i + k) /\ color_at g b == Blue ==>
    getTag (hdr g b) == 0UL \/ (steps_to g0 (page_base i) b /\ hdr g b == hdr g0 b)

/// `blue_ok` reads only the unit's words.
let blue_ok_frame (g0 g g0' g': heap) (i k: nat)
  : Lemma (requires blue_ok g0 g i k /\
                    FR.kept_range g0 g0' (page_base i) (page_base (i + k)) /\
                    FR.kept_range g g' (page_base i) (page_base (i + k)))
          (ensures blue_ok g0' g' i k)
  = let one (b: nat)
      : Lemma (steps_to g' (page_base i) b /\ b < page_base (i + k) /\ color_at g' b == Blue ==>
               getTag (hdr g' b) == 0UL \/ (steps_to g0' (page_base i) b /\ hdr g' b == hdr g0' b))
      = if steps_to g' (page_base i) b && b < page_base (i + k) then begin
          steps_to_le g' (page_base i) b;
          steps_to_frame g' g (page_base i) b;
          FR.kept_hdr g g' (page_base i) (page_base (i + k)) b;
          if steps_to g0 (page_base i) b then begin
            steps_to_frame g0 g0' (page_base i) b;
            FR.kept_hdr g0 g0' (page_base i) (page_base (i + k)) b
          end
        end
    in
    FStar.Classical.forall_intro one

/// An untouched unit.
let kept_blue_ok (g0 g: heap) (i k: nat)
  : Lemma (requires FR.kept_range g0 g (page_base i) (page_base (i + k)))
          (ensures blue_ok g0 g i k)
  = let one (b: nat)
      : Lemma (steps_to g (page_base i) b /\ b < page_base (i + k) ==>
               steps_to g0 (page_base i) b /\ hdr g b == hdr g0 b)
      = if steps_to g (page_base i) b && b < page_base (i + k) then begin
          steps_to_le g (page_base i) b;
          steps_to_frame g g0 (page_base i) b;
          FR.kept_hdr g0 g (page_base i) (page_base (i + k)) b
        end
    in
    FStar.Classical.forall_intro one

/// ---------------------------------------------------------------------------
/// A pool page
/// ---------------------------------------------------------------------------

/// A position the walk over a pool page reaches: a slot start, the filler
/// after a used slot's block, or the tail.
let filler_at (h: heap) (i: nat) (c: nat{c < n_cls}) (j: nat) (b: nat) : prop =
  slot_used h i c j /\ words_at h (slot_base i c j) < cls c /\
  b == slot_base i c j + words_at h (slot_base i c j) * 8

#push-options "--fuel 1"
let rec pool_pos3 (h: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat) (b: nat)
  : Lemma (requires pool_shape h i c /\ k <= n_slots c /\
                    steps_to h (slot_base i c k) b /\ b < page_base (i + 1))
          (ensures (exists (j: nat). j < n_slots c /\ b == slot_base i c j) \/
                   (exists (j: nat). j < n_slots c /\ filler_at h i c j b) \/
                   (tail_words c > 0 /\ b == slots_end i c))
          (decreases (n_slots c - k))
  = slots_fill_page i c;
    page_base_mono (i + 1) n_pages;
    if k = n_slots c then begin
      steps_to_le h (slots_end i c) b;
      assert (tail_words c > 0);
      if b > slots_end i c then begin
        steps_to_refl h (slots_end i c);
        R.block_before h (slots_end i c) (slots_end i c) b
      end
    end else begin
      assert (slot_ok h i c k);
      let a = slot_base i c k in
      slot_base_succ i c k;
      slot_in_page i c k;
      slot_steps h i c k;
      if b = a then ()
      else if b >= slot_base i c (k + 1) then begin
        steps_to_le h a b;
        R.steps_to_det h a (slot_base i c (k + 1)) b;
        pool_pos3 h i c (k + 1) b
      end else begin
        steps_to_refl h a;
        steps_to_le h a b;
        R.block_before h a a b;
        let w = words_at h a in
        if w < cls c && b > a + w * 8 then begin
          steps_to_refl h (a + w * 8);
          R.block_before h (a + w * 8) (a + w * 8) b
        end;
        if w >= cls c then assert False
        else begin
          assert (b == a + w * 8);
          assert (slot_used h i c k);
          assert (filler_at h i c k b)
        end
      end
    end
#pop-options

let slot0 (i: nat) (c: nat{c < n_cls}) : Lemma (slot_base i c 0 == page_base i) = ()

let slot_hdr_tag (c: nat{c < n_cls})
  : Lemma (getTag (PI.slot_hdr c) == 0UL /\ getColor (PI.slot_hdr c) == Blue)
  = cls_bounds c;
    Pool.blue_hdr_tag (cls c)

/// A freed slot start.
let free_start (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (j: nat{j < n_slots c})
  : Lemma (let g' = SP.sw_heap g i c (n_slots c) in
           color_at g' (slot_base i c j) == Blue ==> getTag (hdr g' (slot_base i c j)) == 0UL)
  = let g' = SP.sw_heap g i c (n_slots c) in
    SP.sw_hd g i c (n_slots c) j;
    PI.slot_fits i c j;
    assert (mk_hp_addr (slot_base i c j) == PI.slot_hd i c j);
    SP.whiten_hdr (read_word g (PI.slot_hd i c j));
    slot_hdr_tag c

/// The filler of a survivor's slot is kept, and is a block of the marked page.
let filler_kept (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (j: nat{j < n_slots c}) (b: nat)
  : Lemma (requires pool_shape g i c /\ SP.live g i c j /\
                    filler_at (SP.sw_heap g i c (n_slots c)) i c j b)
          (ensures steps_to g (page_base i) b /\ hdr (SP.sw_heap g i c (n_slots c)) b == hdr g b)
  = let g' = SP.sw_heap g i c (n_slots c) in
    let a = slot_base i c j in
    SP.sw_survivor g i c j;
    SP.live_used g i c j;
    PI.slot_fits i c j;
    assert (mk_hp_addr a == PI.slot_hd i c j);
    SP.whiten_hdr (read_word g (PI.slot_hd i c j));
    assert (words_at g' a == words_at g a);
    slot_base_succ i c j;
    SU.used_pos g i c j;
    block_steps g a (words_at g a);
    steps_to_trans g (page_base i) a b;
    if b < heap_size && b % 8 = 0 then
      assert (read_word g' (mk_hp_addr b) == read_word g (mk_hp_addr b))

/// A dead slot of the swept page is free, so not used.
let dead_not_used (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (j: nat{j < n_slots c})
  : Lemma (requires not (SP.live g i c j))
          (ensures ~(slot_used (SP.sw_heap g i c (n_slots c)) i c j))
  = let g' = SP.sw_heap g i c (n_slots c) in
    SP.sw_hd g i c (n_slots c) j;
    PI.slot_fits i c j;
    assert (mk_hp_addr (slot_base i c j) == PI.slot_hd i c j);
    slot_hdr_tag c

/// The tail of the page is kept, and is a block of the marked page.
let tail_kept (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires pool_shape g i c /\ tail_words c > 0)
          (ensures steps_to g (page_base i) (slots_end i c) /\
                   hdr (SP.sw_heap g i c (n_slots c)) (slots_end i c) == hdr g (slots_end i c))
  = slots_steps g i c (n_slots c);
    slots_fill_page i c;
    page_base_mono (i + 1) n_pages;
    slot_base_aligned i c (n_slots c);
    SP.sw_out g i c (n_slots c) (mk_hp_addr (slots_end i c))

let swept_pool_blue_ok (g: heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires marked_pool_page g pm i c /\ pool_shape (SP.sw_heap g i c (n_slots c)) i c)
          (ensures blue_ok g (SP.sw_heap g i c (n_slots c)) i 1)
  = let g' = SP.sw_heap g i c (n_slots c) in
    let one (b: nat)
      : Lemma (requires steps_to g' (page_base i) b /\ b < page_base (i + 1) /\ color_at g' b == Blue)
              (ensures getTag (hdr g' b) == 0UL \/ (steps_to g (page_base i) b /\ hdr g' b == hdr g b))
      = slot0 i c;
        pool_pos3 g' i c 0 b;
        let start (j: nat) : Lemma (requires j < n_slots c /\ b == slot_base i c j)
                                   (ensures getTag (hdr g' b) == 0UL)
          = free_start g i c j
        in
        let fill (j: nat) : Lemma (requires j < n_slots c /\ filler_at g' i c j b)
                                  (ensures steps_to g (page_base i) b /\ hdr g' b == hdr g b)
          = if SP.live g i c j then filler_kept g i c j b else dead_not_used g i c j
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires start);
        FStar.Classical.forall_intro (FStar.Classical.move_requires fill);
        if tail_words c > 0 && b = slots_end i c then tail_kept g i c
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

let freed_page_blue_ok (g: heap) (i: nat{i < n_pages})
  : Lemma (let (g', _) = SP.page_freed g i in blue_ok g g' i 1)
  = let (g', e) = SP.page_freed g i in
    SP.page_freed_ok g i;
    cls_bounds 0;
    read_write_same g (Init.page_addr i) Init.page_hdr;
    Pool.blue_hdr_tag page_wsize;
    let one (b: nat)
      : Lemma (requires steps_to g' (page_base i) b /\ b < page_base (i + 1))
              (ensures getTag (hdr g' b) == 0UL)
      = MP.free_page_only g' i b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// **A pool page.**
let pool_blue_ok (g: heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires marked_pool_page g pm i c)
          (ensures (let (g', _) = SP.sweep_page g pm i in blue_ok g g' i 1))
  = SP.any_live_spec g i c (n_slots c);
    if SP.any_live g i c (n_slots c) then begin
      SP.sweep_page_correct ();
      let (g', e) = SP.sweep_page g pm i in
      assert (sweep_page_ok g pm i c g' e);
      let k = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun k -> k < n_slots c /\ SP.live g i c k) in
      SP.live_used g i c k;
      swept_pool_blue_ok g pm i c
    end
    else freed_page_blue_ok g i

/// ---------------------------------------------------------------------------
/// A run
/// ---------------------------------------------------------------------------

/// **A run.**  Every free block of the swept run is a block of the layout
/// that is not a survivor, whose header is a new blue header.
let run_blue_ok (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t)
  : Lemma (requires marked_run g pm h)
          (ensures (let (g', _, _) = SR.sweep_run g pm h fp in
                    blue_ok g g' h (run_len (entry pm h).kind)))
  = let n = run_len (entry pm h).kind in
    let s = SR.s_of pm h in
    let e = SR.e_of pm h in
    let fs = SR.lay g pm h in
    let g' = SR.g_of g pm h fp in
    SR.layout_facts g pm h;
    SR.walk_after g pm h fp;
    let one (b: nat)
      : Lemma (requires steps_to g' s b /\ b < e /\ color_at g' b == Blue)
              (ensures getTag (hdr g' b) == 0UL)
      = blk_at_spec fs s e b;
        let c = Some?.v (blk_at fs b) in
        SR.blk_hdr g fs s e fp c;
        FStar.Math.Lemmas.pow2_le_compat 57 54;
        B.bhdr_spec c.w
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)
