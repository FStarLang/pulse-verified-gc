/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.SweepUnits - what sweeping a unit leaves, for the whole sweep
/// ---------------------------------------------------------------------------
///
/// A unit is what the walk covers from a page that does not continue a run:
/// a free page, a pool page or a whole run.  `unit_ok g0 g i k` says that the
/// unit of `k` pages at page `i`, swept from `g0` to `g`, is walked over in
/// `g` and that its blocks are those the sweep must leave:
///   - every block of `g` that is not free was a black block of `g0`, and is
///     that block made white (`whitened_at`);
///   - every black block of `g0` is such a block of `g`.
/// `GC.Spec.Pages.SweepAll` collects these facts unit by unit; at the end
/// they give `no_pointer_to_blue`.
///
/// The facts come from the sweep theorems: `pool_unit_ok` from
/// `sweep_page_ok`, `run_unit_ok` from `sweep_run_ok`, and `free_unit_ok`
/// for a free page, which the sweep leaves alone.  `unit_ok_frame` keeps
/// them while other units are swept.

module GC.Spec.Pages.SweepUnits

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

module U64 = FStar.UInt64
module Seq = FStar.Seq
module R = GC.Spec.Pages.Replace
module B = GC.Spec.Pages.Blocks
module F = GC.Spec.Pages.Frame
module PI = GC.Spec.Pages.PoolInit

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let unit_ok (g0 g: heap) (i k: nat) : prop =
  steps_to g (page_base i) (page_base (i + k)) /\
  (forall (b: nat). steps_to g (page_base i) b /\ b < page_base (i + k) /\ color_at g b =!= Blue ==>
     steps_to g0 (page_base i) b /\ color_at g0 b == Black /\ whitened_at g0 g b) /\
  (forall (b: nat). steps_to g0 (page_base i) b /\ b < page_base (i + k) /\ color_at g0 b == Black ==>
     steps_to g (page_base i) b /\ whitened_at g0 g b)

/// ---------------------------------------------------------------------------
/// Frames
/// ---------------------------------------------------------------------------

/// `whitened_at` reads the block's words only.
let whitened_frame (g0 g g0' g': heap) (lo hi: nat) (b: nat)
  : Lemma (requires F.kept_range g0 g0' lo hi /\ F.kept_range g g' lo hi /\
                    lo <= b /\ b + words_at g0 b * 8 <= hi /\ whitened_at g0 g b)
          (ensures whitened_at g0' g' b)
  = F.kept_hdr g0 g0' lo hi b;
    F.kept_hdr g g' lo hi b

/// A unit's facts read only its words.
let unit_ok_frame (g0 g g0' g': heap) (i k: nat)
  : Lemma (requires unit_ok g0 g i k /\
                    F.kept_range g0 g0' (page_base i) (page_base (i + k)) /\
                    F.kept_range g g' (page_base i) (page_base (i + k)))
          (ensures unit_ok g0' g' i k)
  = let s = page_base i in
    let e = page_base (i + k) in
    steps_to_frame g g' s e;
    let pos (h0 h1: heap) (b: nat)
      : Lemma (requires F.kept_range h0 h1 s e /\ b <= e)
              (ensures steps_to h1 s b == steps_to h0 s b)
      = steps_to_frame h0 h1 s b
    in
    let ext (h: heap) (b: nat)
      : Lemma (requires steps_to h s b /\ b < e /\ steps_to h s e)
              (ensures b + words_at h b * 8 <= e)
      = R.block_before h s b e
    in
    let a1 (b: nat)
      : Lemma (requires steps_to g' s b /\ b < e /\ color_at g' b =!= Blue)
              (ensures steps_to g0' s b /\ color_at g0' b == Black /\ whitened_at g0' g' b)
      = pos g g' b;
        pos g0 g0' b;
        steps_to_le g s b;
        F.kept_hdr g g' s e b;
        F.kept_hdr g0 g0' s e b;
        ext g b;
        colorHeader_preserves_wosize (hdr g0 b) White;
        whitened_frame g0 g g0' g' s e b
    in
    let a2 (b: nat)
      : Lemma (requires steps_to g0' s b /\ b < e /\ color_at g0' b == Black)
              (ensures steps_to g' s b /\ whitened_at g0' g' b)
      = pos g g' b;
        pos g0 g0' b;
        steps_to_le g0 s b;
        F.kept_hdr g0 g0' s e b;
        ext g b;
        colorHeader_preserves_wosize (hdr g0 b) White;
        whitened_frame g0 g g0' g' s e b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires a1);
    FStar.Classical.forall_intro (FStar.Classical.move_requires a2)

/// ---------------------------------------------------------------------------
/// The blocks of a pool page
/// ---------------------------------------------------------------------------

/// A position the walk over a pool page reaches is a slot start or a free
/// block (a free slot, a filler or the tail).
let rec pool_pos_from (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat) (b: nat)
  : Lemma (requires pool_shape g i c /\ k <= n_slots c /\
                    steps_to g (slot_base i c k) b /\ b < page_base (i + 1))
          (ensures (exists (j: nat). j < n_slots c /\ b == slot_base i c j /\ slot_used g i c j) \/
                   color_at g b == Blue)
          (decreases (n_slots c - k))
  = slots_fill_page i c;
    page_base_mono (i + 1) n_pages;
    if k = n_slots c then begin
      (* the tail: one blue block *)
      steps_to_le g (slots_end i c) b;
      assert (tail_words c > 0);
      if b > slots_end i c then begin
        steps_to_refl g (slots_end i c);
        R.block_before g (slots_end i c) (slots_end i c) b
      end
    end else begin
      assert (slot_ok g i c k);
      let a = slot_base i c k in
      slot_base_succ i c k;
      slot_in_page i c k;
      slot_steps g i c k;
      if b = a then ()
      else if b >= slot_base i c (k + 1) then begin
        steps_to_le g a b;
        R.steps_to_det g a (slot_base i c (k + 1)) b;
        pool_pos_from g i c (k + 1) b
      end else begin
        (* inside slot k, past its start: the filler of a used slot *)
        steps_to_refl g a;
        steps_to_le g a b;
        R.block_before g a a b;
        if words_at g a < cls c && b > a + words_at g a * 8 then begin
          steps_to_refl g (a + words_at g a * 8);
          R.block_before g (a + words_at g a * 8) (a + words_at g a * 8) b
        end
      end
    end

/// The used slots of a pool page are walk positions.
let used_pos (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (requires pool_shape g i c)
          (ensures steps_to g (page_base i) (slot_base i c k) /\ slot_base i c k < page_base (i + 1))
  = slots_steps g i c k;
    slot_in_page i c k;
    slots_fill_page i c

let whitened_whitened_at (g g': heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (requires whitened g g' (PI.slot_hd i c k))
          (ensures whitened_at g g' (slot_base i c k))
  = PI.slot_fits i c k;
    assert (mk_hp_addr (slot_base i c k) == PI.slot_hd i c k)

/// **A swept pool page has its unit's facts.**
let pool_unit_ok (g g': heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (e: page_info)
  : Lemma (requires marked_pool_page g pm i c /\ sweep_page_ok g pm i c g' e)
          (ensures unit_ok g g' i 1)
  = let s = page_base i in
    let t = page_base (i + 1) in
    pool_steps g i c;
    if e.kind = Free then begin
      free_page_steps g' i;
      let a1 (b: nat)
        : Lemma (requires steps_to g' s b /\ b < t /\ color_at g' b =!= Blue) (ensures False)
        = steps_to_le g' s b;
          if b > s then begin
            steps_to_refl g' s;
            R.block_before g' s s b;
            FStar.Math.Lemmas.distributivity_add_left i 1 page_bytes
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires a1);
      let a2 (b: nat)
        : Lemma (requires steps_to g s b /\ b < t /\ color_at g b == Black) (ensures False)
        = PI.slot_fits i c 0;
          pool_pos_from g i c 0 b;
          assert (~(exists (k: nat). k < n_slots c /\ slot_used g i c k /\
                      color_at g (slot_base i c k) == Black))
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires a2)
    end else begin
      pool_steps g' i c;
      let a1 (b: nat)
        : Lemma (requires steps_to g' s b /\ b < t /\ color_at g' b =!= Blue)
                (ensures steps_to g s b /\ color_at g b == Black /\ whitened_at g g' b)
        = pool_pos_from g' i c 0 b;
          eliminate exists (j: nat). j < n_slots c /\ b == slot_base i c j /\ slot_used g' i c j
          with begin
            if not (slot_used g i c j && color_at g (slot_base i c j) = Black) then
              assert (slot_free g' i c j)
            else begin
              used_pos g i c j;
              whitened_whitened_at g g' i c j
            end
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires a1);
      let a2 (b: nat)
        : Lemma (requires steps_to g s b /\ b < t /\ color_at g b == Black)
                (ensures steps_to g' s b /\ whitened_at g g' b)
        = pool_pos_from g i c 0 b;
          eliminate exists (j: nat). j < n_slots c /\ b == slot_base i c j /\ slot_used g i c j
          with begin
            used_pos g' i c j;
            whitened_whitened_at g g' i c j
          end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires a2)
    end

/// **A swept run has its unit's facts.**
let run_unit_ok (g g': heap) (pm pm': page_map) (h: nat{h < n_pages}) (fp fp': U64.t)
  : Lemma (requires marked_run g pm h /\ sweep_run_ok g pm h fp g' pm' fp')
          (ensures unit_ok g g' h (run_len (entry pm h).kind))
  = ()

/// **A free page has its unit's facts**, when it is left alone.
let free_unit_ok (g0 g: heap) (i: nat{i < n_pages})
  : Lemma (requires free_page_shape g0 i /\ F.kept_range g0 g (page_base i) (page_base (i + 1)))
          (ensures unit_ok g0 g i 1)
  = let s = page_base i in
    let t = page_base (i + 1) in
    free_page_steps g0 i;
    let only (h: heap) (b: nat)
      : Lemma (requires free_page_shape h i /\ steps_to h s b /\ b < t)
              (ensures b == s)
      = steps_to_le h s b;
        if b > s then begin
          steps_to_refl h s;
          R.block_before h s s b;
          FStar.Math.Lemmas.distributivity_add_left i 1 page_bytes
        end
    in
    F.kept_hdr g0 g s t s;
    page_base_mono i (i + 1);
    FStar.Math.Lemmas.distributivity_add_left i 1 page_bytes;
    assert (free_page_shape g i);
    free_page_steps g i;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (only g));
    FStar.Classical.forall_intro (FStar.Classical.move_requires (only g0))
