/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.SweepStarts - where the sweep's free blocks start
/// ---------------------------------------------------------------------------
///
/// `starts_ok g0 g i k`: every free block of the walk over the unit of `k`
/// pages at page `i`, swept from `g0` to `g`, starts where a block of `g0`
/// started, or at the start of a page.
///   - A pool page's free blocks are its slots, the fillers of its survivors
///     and its tail, all blocks of the marked page; a freed page starts at
///     its page.
///   - A run's free blocks are its merged dead stretches, which start where
///     their first dead block did, and the pieces the split cuts at page
///     starts (`GC.Spec.Pages.RunList`).
///
/// So the sweep never starts a free block inside a block of the marked heap,
/// except at a page start.  `GC.Spec.Pages.Collect` uses this for the last
/// word of the heap: a block there would be too short to be an object, and
/// no page starts there.
///
/// `inv3` carries the facts through the whole sweep, as
/// `GC.Spec.Pages.SweepWf.inv2` carries the tag facts.

module GC.Spec.Pages.SweepStarts

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
open GC.Spec.Pages.RunList
open GC.Spec.Pages.SweepAll

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module R = GC.Spec.Pages.Replace
module FR = GC.Spec.Pages.Frame
module SP = GC.Spec.Pages.SweepPage
module SR = GC.Spec.Pages.SweepRun
module ST = GC.Spec.Pages.SweepTags
module SW = GC.Spec.Pages.SweepWf
module MP = GC.Spec.Pages.MarkPhase

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let is_page_start (b: nat) : prop = exists (j: nat). b == page_base j

let starts_ok (g0 g: heap) (i k: nat) : prop =
  forall (b: nat).
    steps_to g (page_base i) b /\ b < page_base (i + k) /\ color_at g b == Blue ==>
    steps_to g0 (page_base i) b \/ is_page_start b

/// `starts_ok` reads only the unit's words.
let starts_ok_frame (g0 g g0' g': heap) (i k: nat)
  : Lemma (requires starts_ok g0 g i k /\
                    FR.kept_range g0 g0' (page_base i) (page_base (i + k)) /\
                    FR.kept_range g g' (page_base i) (page_base (i + k)))
          (ensures starts_ok g0' g' i k)
  = let one (b: nat)
      : Lemma (steps_to g' (page_base i) b /\ b < page_base (i + k) /\ color_at g' b == Blue ==>
               steps_to g0' (page_base i) b \/ is_page_start b)
      = if steps_to g' (page_base i) b && b < page_base (i + k) then begin
          steps_to_le g' (page_base i) b;
          steps_to_frame g' g (page_base i) b;
          FR.kept_hdr g g' (page_base i) (page_base (i + k)) b;
          steps_to_frame g0 g0' (page_base i) b
        end
    in
    FStar.Classical.forall_intro one

/// An untouched unit.
let kept_starts_ok (g0 g: heap) (i k: nat)
  : Lemma (requires FR.kept_range g0 g (page_base i) (page_base (i + k)))
          (ensures starts_ok g0 g i k)
  = let one (b: nat)
      : Lemma (steps_to g (page_base i) b /\ b < page_base (i + k) ==> steps_to g0 (page_base i) b)
      = if steps_to g (page_base i) b && b < page_base (i + k) then begin
          steps_to_le g (page_base i) b;
          steps_to_frame g g0 (page_base i) b
        end
    in
    FStar.Classical.forall_intro one

/// ---------------------------------------------------------------------------
/// A pool page
/// ---------------------------------------------------------------------------

let swept_pool_starts (g: heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires marked_pool_page g pm i c /\ pool_shape (SP.sw_heap g i c (n_slots c)) i c)
          (ensures starts_ok g (SP.sw_heap g i c (n_slots c)) i 1)
  = let g' = SP.sw_heap g i c (n_slots c) in
    let one (b: nat)
      : Lemma (requires steps_to g' (page_base i) b /\ b < page_base (i + 1) /\ color_at g' b == Blue)
              (ensures steps_to g (page_base i) b)
      = ST.slot0 i c;
        ST.pool_pos3 g' i c 0 b;
        let start (j: nat) : Lemma (requires j < n_slots c /\ b == slot_base i c j)
                                   (ensures steps_to g (page_base i) b)
          = slots_steps g i c j
        in
        let fill (j: nat) : Lemma (requires j < n_slots c /\ ST.filler_at g' i c j b)
                                  (ensures steps_to g (page_base i) b)
          = if SP.live g i c j then ST.filler_kept g i c j b else ST.dead_not_used g i c j
        in
        FStar.Classical.forall_intro (FStar.Classical.move_requires start);
        FStar.Classical.forall_intro (FStar.Classical.move_requires fill);
        if tail_words c > 0 && b = slots_end i c then ST.tail_kept g i c
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

let freed_page_starts (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (let (g', _) = SP.page_freed g i c in starts_ok g g' i 1)
  = let (g', e) = SP.page_freed g i c in
    SP.page_freed_ok g i c;
    let one (b: nat)
      : Lemma (requires steps_to g' (page_base i) b /\ b < page_base (i + 1))
              (ensures is_page_start b)
      = MP.free_page_only g' i b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// **A pool page.**
let pool_starts (g: heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires marked_pool_page g pm i c)
          (ensures (let (g', _) = SP.sweep_page g pm i in starts_ok g g' i 1))
  = SP.any_live_spec g i c (n_slots c);
    if SP.any_live g i c (n_slots c) then begin
      SP.sweep_page_correct ();
      let (g', e) = SP.sweep_page g pm i in
      assert (sweep_page_ok g pm i c g' e);
      let k = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun k -> k < n_slots c /\ SP.live g i c k) in
      SP.live_used g i c k;
      swept_pool_starts g pm i c
    end
    else freed_page_starts g i c

/// ---------------------------------------------------------------------------
/// A run
/// ---------------------------------------------------------------------------

let ats (bs: list blk) : list nat = L.map (fun (b: blk) -> b.at) bs

/// The blocks of the walk start where the walk goes.
#push-options "--fuel 1 --ifuel 1"
let rec olds_at (g: heap) (s a e: nat) (x: nat)
  : Lemma (requires steps_to g s a /\ steps_to g a e /\ L.mem x (ats (olds g a e)))
          (ensures steps_to g s x)
          (decreases (if a < e then e - a else 0))
  = steps_to_le g a e;
    if a >= e then ()
    else begin
      let ha = mk_hp_addr a in
      steps_to_next g ha e;
      R.block_bytes_words g a;
      let a' = a + words_at g a * 8 in
      if x = a then ()
      else begin
        steps_to_one g ha a';
        steps_to_trans g s a a';
        olds_at g s a' e x
      end
    end
#pop-options

/// A merged block starts where one of its blocks did.
#push-options "--fuel 2 --ifuel 2"
let rec merge_at (bs: list blk) (c: blk)
  : Lemma (requires L.mem c (merge bs)) (ensures L.mem c.at (ats bs)) (decreases bs)
  = match bs with
    | [] -> ()
    | b :: bs' ->
      let m = merge bs' in
      if b.t = Live then (if c = b then () else merge_at bs' c)
      else match m with
           | d :: m' ->
             if d.t = Live then (if c.at = b.at then () else merge_at bs' c)
             else (if c.at = b.at then () else merge_at bs' c)
           | [] -> ()
#pop-options

/// A piece of the split starts where its block did, or at a page start.
#push-options "--fuel 2 --ifuel 2"
let split1_at (b: blk) (c: blk)
  : Lemma (requires L.mem c (split1 b)) (ensures c.at == b.at \/ is_page_start c.at)
  = if b.t <> Dead then ()
    else begin
      let r = b.at in
      let e = bend b in
      let p = pg_ceil r in
      let q = pg_floor e in
      if r < z || p >= q then ()
      else begin
        L.append_mem (pre_of r p) (L.append (pages p q) (suf_of q e)) c;
        L.append_mem (pages p q) (suf_of q e) c;
        if L.mem c (pages p q) then begin
          pages_spec p q;
          eliminate exists (j: nat). p <= j /\ j < q /\ c == page_blk j
          with ()
        end
      end
    end

let rec split_at (bs: list blk) (c: blk)
  : Lemma (requires L.mem c (split bs)) (ensures L.mem c.at (ats bs) \/ is_page_start c.at)
          (decreases bs)
  = match bs with
    | [] -> ()
    | b :: bs' ->
      L.append_mem (split1 b) (split bs') c;
      if L.mem c (split1 b) then split1_at b c
      else split_at bs' c
#pop-options

/// **A run.**
let run_starts (g: heap) (pm: page_map) (h: nat{h < n_pages}) (fp: U64.t)
  : Lemma (requires marked_run g pm h)
          (ensures (let (g', _, _) = SR.sweep_run g pm h fp in
                    starts_ok g g' h (run_len (entry pm h).kind)))
  = let s = SR.s_of pm h in
    let e = SR.e_of pm h in
    let fs = SR.lay g pm h in
    let g' = SR.g_of g pm h fp in
    SR.layout_facts g pm h;
    SR.walk_after g pm h fp;
    let one (b: nat)
      : Lemma (requires steps_to g' s b /\ b < e)
              (ensures steps_to g s b \/ is_page_start b)
      = blk_at_spec fs s e b;
        let c = Some?.v (blk_at fs b) in
        split_at (merge (olds g s e)) c;
        if L.mem c.at (ats (merge (olds g s e))) then begin
          FStar.List.Tot.Properties.memP_map_elim (fun (b: blk) -> b.at) c.at (merge (olds g s e));
          eliminate exists (d: blk). L.memP d (merge (olds g s e)) /\ d.at == c.at
          with begin
            L.mem_memP d (merge (olds g s e));
            merge_at (olds g s e) d;
            steps_to_refl g s;
            olds_at g s s e c.at
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// ---------------------------------------------------------------------------
/// Through the sweep
/// ---------------------------------------------------------------------------

let starts_before (g0: heap) (st0: pstate) (g: heap) (p: nat) : prop =
  forall (i: nat{i < n_pages}). i < p /\ walk_page st0.pm i ==> starts_ok g0 g i (span st0.pm i)

let inv3 (g0: heap) (st0: pstate) (g: heap) (st: pstate) (p: nat) : prop =
  SW.inv2 g0 st0 g st p /\ starts_before g0 st0 g p

/// The new unit's facts, against the marked heap.
let step_starts (g0 g: heap) (st0 st: pstate) (p: nat{p < n_pages})
  : Lemma (requires sweep_ready g0 st0 /\ inv g0 st0 g st p)
          (ensures (let (g', _) = step g st p in starts_ok g0 g' p (span st0.pm p)))
  = inv_elim g0 st0 g st p;
    let (g', st') = step g st p in
    let k = span st0.pm p in
    assert (FR.kept_range g g0 (page_base p) (page_base (p + k)));
    page_base_mono p (p + k);
    match (entry st0.pm p).kind with
    | Free ->
      kept_starts_ok g0 g p k
    | Pool c ->
      marked_pool_at g0 g st0 st p c;
      pool_starts g st.pm p c;
      starts_ok_frame g g' g0 g' p k
    | LargeHead _ ->
      marked_run_at g0 g st0 st p;
      run_starts g st.pm p (GC.Spec.Pages.Cells.large_head st);
      starts_ok_frame g g' g0 g' p k

let inv3_step (g0 g: heap) (st0 st: pstate) (p: nat{p < n_pages})
  : Lemma (requires sweep_ready g0 st0 /\ inv3 g0 st0 g st p)
          (ensures (let (g', st') = step g st p in inv3 g0 st0 g' st' (p + span st.pm p)))
  = inv_elim g0 st0 g st p;
    SW.inv2_step g0 g st0 st p;
    SW.step_frame g0 g st0 st p;
    let (g', st') = step g st p in
    let k = span st0.pm p in
    assert (map_ok st0.pm);
    next_walk_page st0.pm p p;
    let old (i: nat{i < n_pages})
      : Lemma (i < p + k /\ walk_page st0.pm i ==> starts_ok g0 g' i (span st0.pm i))
      = if i < p + k && walk_page st0.pm i then begin
          if i < p then begin
            assert (i + span st0.pm i <= p);
            page_base_mono (i + span st0.pm i) p;
            starts_ok_frame g0 g g0 g' i (span st0.pm i)
          end
          else if i = p then step_starts g0 g st0 st p
          else next_walk_page st0.pm p i
        end
    in
    FStar.Classical.forall_intro old

#push-options "--fuel 1"
let rec sweep_from_inv3 (g0 g: heap) (st0 st: pstate) (p: nat)
  : Lemma (requires sweep_ready g0 st0 /\ inv3 g0 st0 g st p)
          (ensures (let (g', st') = sweep_from g st p in inv3 g0 st0 g' st' n_pages))
          (decreases (if p < n_pages then n_pages - p else 0))
  = inv_bound g0 st0 g st p;
    if p >= n_pages then ()
    else begin
      inv3_step g0 g st0 st p;
      let (g', st') = step g st p in
      sweep_from_inv3 g0 g' st0 st' (p + span st.pm p)
    end
#pop-options

/// **The whole sweep.**
let sweep_all_inv3 (g: heap) (st: pstate)
  : Lemma (requires sweep_ready g st)
          (ensures (let (g', st') = sweep_all g st in inv3 g st g' st' n_pages))
  = SW.inv2_init g st;
    sweep_from_inv3 g g st st 0
