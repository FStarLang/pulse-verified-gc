/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesFree - the page sweep with "free" meaning blue (G16)
/// ---------------------------------------------------------------------------
///
/// The page modules state the sweep with `free_sw pm`: a block is free when
/// it is blue, or white on a page not yet swept.  So their step lemma
/// (`MidSweepStep.step_sw`) says that the set of blocks in use does not
/// change: a dead object counts as free before the sweep reaches it.
///
/// The top-level specification counts as free only what is free: a blue
/// block (`free_true`, which is `free_stw`).  Then a sweep step does free
/// something.  This module restates one step of the page sweep in that form:
///   - `step_frees_white`: after `SweepAll.step` on an unswept unit (a pool
///     page, or a large run), a block is in use exactly when it was in use
///     and was not a white block of the unit.  Nothing else changes status.
///   - `freed_words_of`: the words a step frees, the size (header included)
///     of the white blocks of the unit before the step; it is what the
///     specification's `freed_words` counts (`swept_words`), read at the byte
///     level;
///   - `step_frees_words`, word by word: inside the unit, a byte is in a blue
///     block after the step exactly when it was in a blue (free) or white
///     (freed) block before; outside it nothing moves.  Free words grow by
///     exactly the words of the white blocks.
///
/// The unit's facts (`MidSweepStep.swept_unit`: the stretch rewritten in
/// place, survivors whitened, the unit's pages turned swept and no other
/// page's bit changed) are established inside `MidSweepStep.pool_step_sw` and
/// `run_step_sw` but not exported; `pool_unit` and `run_unit` derive them
/// again here, with the same steps, from the same exported lemmas.

module GC.Spec.Top.PagesFree

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
open GC.Spec.Pages.Frame
open GC.Spec.Pages.MidSweep
open GC.Spec.Pages.MidSweepStep
module U64 = FStar.UInt64
module Seq = FStar.Seq
module G = GC.Spec.Pages.Graft
module Th = GC.Spec.Pages.Theorems
module SU = GC.Spec.Pages.SweepUnits
module SS = GC.Spec.Pages.SweepStep
module SA = GC.Spec.Pages.SweepAll
module SP = GC.Spec.Pages.SweepPage
module SR = GC.Spec.Pages.SweepRun
module ST = GC.Spec.Pages.SweepTags
module Cells = GC.Spec.Pages.Cells
module Rp = GC.Spec.Pages.Replace

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// Truly free: blue.
let free_true : free_def = free_stw

/// The unit of page `p`: its pages, `[page_base p, page_base (p + span))`.
let in_unit (pm: page_map) (p: nat{p < n_pages}) (x: obj_addr) : bool =
  page_base p <= U64.v x - 8 && U64.v x - 8 < page_base (p + span pm p)

/// ---------------------------------------------------------------------------
/// The unit, again
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40"
let pool_unit (g: heap) (st: pstate) (p: nat{p < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires pages_ok_sw g st /\ (entry st.pm p).kind == Pool c /\ not (entry st.pm p).swept)
          (ensures (let (g', st') = SA.step g st p in swept_unit g g' st.pm st'.pm p 1))
  = let pm = st.pm in
    pages_ok_sw_elim g st;
    assert (page_local g pm p);
    assert (Th.marked_pool_page g pm p c);
    let cs = Cells.walk g (Cells.large_head st) heap_words in
    Cells.large_ok_lview g st;
    SS.pool_step g st p c cs;
    let (g', e) = SP.sweep_page g pm p in
    let st' = SS.push_avail st p e in
    let pm' = st'.pm in
    assert (SA.step g st p == (g', st'));
    walk_pages_reached g pm p;
    page_steps g pm p;
    page_base_mono p (p + 1);
    page_base_mono (p + 1) n_pages;
    ST.pool_blue_ok g pm p c;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (pool_no_grey g pm p c));
    unit_one pm pm' p;
    unit_uw pm pm' p 1;
    assert (swept_unit g g' pm pm' p 1)

let run_unit (g: heap) (st: pstate) (p: nat{p < n_pages}) (n: pos)
  : Lemma (requires pages_ok_sw g st /\ (entry st.pm p).kind == LargeHead n /\ not (entry st.pm p).swept)
          (ensures (let (g', st') = SA.step g st p in swept_unit g g' st.pm st'.pm p n))
  = let pm = st.pm in
    pages_ok_sw_elim g st;
    assert (page_local g pm p);
    assert (run_ok pm p);
    assert (Th.marked_run g pm p);
    let cs = Cells.walk g (Cells.large_head st) heap_words in
    Cells.large_ok_lview g st;
    SS.run_step g st p n cs;
    let (g', pm', fp') = SR.sweep_run g pm p (Cells.large_head st) in
    let st' = SS.run_state st pm' fp' in
    assert (SA.step g st p == (g', st'));
    eliminate exists (cs': list obj_addr). Cells.lview g' st' cs'
    with Cells.lview_large_ok g' st' cs';
    walk_pages_reached g pm p;
    page_base_mono p (p + n);
    page_base_mono (p + n) n_pages;
    ST.run_blue_ok g pm p (Cells.large_head st);
    let in_unit (j: nat{j < n_pages})
      : Lemma (p <= j /\ j < p + n ==> not (entry pm j).swept /\ (entry pm' j).swept)
      = if p < j && j < p + n then assert ((entry pm j).swept == (entry pm p).swept)
    in
    FStar.Classical.forall_intro in_unit;
    let off_unit (j: nat{j < n_pages})
      : Lemma (j < p \/ j >= p + n ==> (entry pm' j).swept == (entry pm j).swept) = ()
    in
    FStar.Classical.forall_intro off_unit;
    unit_uw pm pm' p n;
    assert (swept_unit g g' pm pm' p n)
#pop-options

/// ---------------------------------------------------------------------------
/// One step, with free meaning blue
/// ---------------------------------------------------------------------------

/// From the unit's facts: inside the unit, the blocks in use after are the
/// blocks in use and not white before; outside it, nothing changes status.
let unit_frees_white (g g': heap) (pm pm': page_map) (p k: nat) (y: obj_addr)
  : Lemma (requires swept_unit g g' pm pm' p k /\ use_kept g g' pm pm')
          (ensures in_use free_true g' y ==
                   (in_use free_true g y &&
                    not (page_base p <= U64.v y - 8 && U64.v y - 8 < page_base (p + k) && is_white y g)))
  = let h = U64.v y - 8 in
    colours g y; colours g' y;
    hd_address_spec y;
    if page_base p <= h && h < page_base (p + k) then begin
      (* inside: unswept before, swept after; use_kept at free_sw *)
      assert (G.uw pm h /\ not (G.uw pm' h));
      assert (in_use (free_sw pm') g' y == in_use (free_sw pm) g y)
    end
    else begin
      (* outside: same object, same header *)
      unit_obj_out g g' (page_base p) (page_base (p + k)) y;
      if Seq.mem y (objects zero_addr g) then begin
        assert (read_word g' (hd_address y) == read_word g (hd_address y));
        color_of_object_spec y g; color_of_object_spec y g'
      end
    end

/// The restated step (G16): `SweepAll.step` on an unswept pool page or large
/// run frees exactly the white blocks of its unit.
let step_frees_white (g: heap) (st: pstate) (p: nat{p < n_pages}) (y: obj_addr)
  : Lemma (requires pages_ok_sw g st /\ not (entry st.pm p).swept /\
                    (Pool? (entry st.pm p).kind \/ LargeHead? (entry st.pm p).kind))
          (ensures (let (g', st') = SA.step g st p in
                    in_use free_true g' y ==
                    (in_use free_true g y && not (in_unit st.pm p y && is_white y g))))
  = let pm = st.pm in
    step_sw g st p;
    let (g', st') = SA.step g st p in
    pages_ok_sw_elim g st;
    assert (run_ok pm p /\ free_ok pm p);
    match (entry pm p).kind with
    | Pool c ->
      pool_unit g st p c;
      assert (span pm p == 1);
      unit_frees_white g g' pm st'.pm p 1 y
    | LargeHead n ->
      run_unit g st p n;
      assert (span pm p == n);
      unit_frees_white g g' pm st'.pm p n y

/// ---------------------------------------------------------------------------
/// The words a step frees
/// ---------------------------------------------------------------------------

/// The white blocks of the unit, before the step: what it frees.
let freed_block (g: heap) (pm: page_map) (p: nat{p < n_pages}) (x: obj_addr) : GTot bool =
  in_use free_true g x && in_unit pm p x && is_white x g

let rec freed_in (g: heap) (pm: page_map) (p: nat{p < n_pages}) (s: Seq.seq obj_addr)
  : GTot nat (decreases Seq.length s) =
  if Seq.length s = 0 then 0
  else (if freed_block g pm p (Seq.head s) then whsize g (Seq.head s) else 0) +
       freed_in g pm p (Seq.tail s)

/// `freed_words` of one page-sweep step: the words (headers included) of the
/// white blocks of its unit.
let freed_words_of (g: heap) (pm: page_map) (p: nat{p < n_pages}) : GTot nat =
  freed_in g pm p (objects zero_addr g)

/// The blocks it counts are exactly the ones the step frees.
let freed_words_counts (g: heap) (st: pstate) (p: nat{p < n_pages}) (y: obj_addr)
  : Lemma (requires pages_ok_sw g st /\ not (entry st.pm p).swept /\
                    (Pool? (entry st.pm p).kind \/ LargeHead? (entry st.pm p).kind))
          (ensures (let (g', st') = SA.step g st p in
                    freed_block g st.pm p y <==> (in_use free_true g y /\ not (in_use free_true g' y))))
  = step_frees_white g st p y

/// ---------------------------------------------------------------------------
/// In the model
/// ---------------------------------------------------------------------------

/// Read through the abstraction, free means a blue block: a model block is
/// in use exactly when the byte-level object is in use with free meaning
/// blue.
let abs_in_use (g: heap) (m: nat)
  : Lemma (requires GC.Spec.Top.Heap.is_block (GC.Spec.Top.Abs.abs g) m)
          (ensures GC.Spec.Top.Abs.pos m + 8 < heap_size /\
                   (GC.Spec.Top.Heap.col_of (GC.Spec.Top.Abs.abs g) m <> GC.Spec.Top.Heap.Blue <==>
                    in_use free_true g (GC.Spec.Top.Abs.obj_of m)))
  = GC.Spec.Top.Abs.abs_is_block g m;
    GC.Spec.Top.Abs.abs_blue g m

/// ---------------------------------------------------------------------------
/// Free words grow exactly
/// ---------------------------------------------------------------------------

/// The block of the walk from `s` (to `e`) that covers byte `w`.
let covering (g: heap) (s e: nat) (b w: nat) : prop =
  steps_to g s b /\ b < e /\ b <= w /\ w < b + words_at g b * 8

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let rec cover_exists (g: heap) (s e w: nat)
  : Lemma (requires steps_to g s e /\ s <= w /\ w < e)
          (ensures exists (b: nat). covering g s e b w)
          (decreases (e - s))
  = steps_to_le g s e;
    let sa = mk_hp_addr s in
    steps_to_next g sa e;
    let n = s + block_bytes g sa in
    Rp.block_bytes_words g s;
    steps_to_refl g s;
    if w < n then assert (covering g s e s w)
    else begin
      cover_exists g n e w;
      let b = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun b -> covering g n e b w) in
      steps_to_one g sa n;
      steps_to_trans g s n b;
      assert (covering g s e b w)
    end
#pop-options

let cover_unique (g: heap) (s e b1 b2 w: nat)
  : Lemma (requires covering g s e b1 w /\ covering g s e b2 w) (ensures b1 == b2)
  = if b1 < b2 then Rp.block_before g s b1 b2
    else if b2 < b1 then Rp.block_before g s b2 b1

/// The bytes of the unit covered by a block of colour `c` (of a set).
let covered_by (g: heap) (s e w: nat) (ok: color_sem -> bool) : prop =
  exists (b: nat). covering g s e b w /\ ok (color_at g b)

let is_blue_c (c: color_sem) : bool = c = Blue
let is_free_or_freed (c: color_sem) : bool = c = Blue || c = White

/// One step of the page sweep, word by word: inside its unit, a byte is in
/// a blue block after the step exactly when it was in a blue block (free) or
/// a white one (freed) before.  Outside it nothing moves (`unit_step`).
#push-options "--z3rlimit 40"
let unit_words (g g': heap) (pm pm': page_map) (p k: nat) (w: nat)
  : Lemma (requires swept_unit g g' pm pm' p k /\ page_base p <= w /\ w < page_base (p + k))
          (ensures covered_by g' (page_base p) (page_base (p + k)) w is_blue_c <==>
                   covered_by g (page_base p) (page_base (p + k)) w is_free_or_freed)
  = let s = page_base p in
    let e = page_base (p + k) in
    assert (steps_to g s e /\ steps_to g' s e);
    assert (SU.unit_ok g g' p k);
    cover_exists g s e w;
    cover_exists g' s e w;
    let b = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun b -> covering g s e b w) in
    let b' = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun b -> covering g' s e b w) in
    (* the block covering w before: not grey *)
    assert (color_at g b =!= Gray);
    (* a black block survives, whitened, same size *)
    if color_at g b = Black then begin
      assert (steps_to g' s b /\ Th.whitened_at g g' b);
      whitened_colour g g' b;
      assert (covering g' s e b w);
      cover_unique g' s e b b' w;
      let no (x: nat) : Lemma (covering g s e x w ==> x == b) = FStar.Classical.move_requires (cover_unique g s e x b) w in
      FStar.Classical.forall_intro no;
      let no' (x: nat) : Lemma (covering g' s e x w ==> x == b) = FStar.Classical.move_requires (cover_unique g' s e x b) w in
      FStar.Classical.forall_intro no'
    end
    else begin
      (* a block not blue after was a black block before *)
      if color_at g' b' <> Blue then begin
        assert (steps_to g s b' /\ color_at g b' == Black /\ Th.whitened_at g g' b');
        whitened_colour g g' b';
        assert (covering g s e b' w);
        cover_unique g s e b b' w
      end;
      let no (x: nat) : Lemma (covering g s e x w ==> x == b) = FStar.Classical.move_requires (cover_unique g s e x b) w in
      FStar.Classical.forall_intro no;
      let no' (x: nat) : Lemma (covering g' s e x w ==> x == b') = FStar.Classical.move_requires (cover_unique g' s e x b') w in
      FStar.Classical.forall_intro no'
    end
#pop-options

/// The restated step, word by word (G16): `SweepAll.step` on an unswept pool
/// page or large run makes free exactly the words that were free or in a
/// white block of its unit.
let step_frees_words (g: heap) (st: pstate) (p: nat{p < n_pages}) (w: nat)
  : Lemma (requires pages_ok_sw g st /\ not (entry st.pm p).swept /\
                    (Pool? (entry st.pm p).kind \/ LargeHead? (entry st.pm p).kind) /\
                    page_base p <= w /\ w < page_base (p + span st.pm p))
          (ensures (let (g', st') = SA.step g st p in
                    covered_by g' (page_base p) (page_base (p + span st.pm p)) w is_blue_c <==>
                    covered_by g (page_base p) (page_base (p + span st.pm p)) w is_free_or_freed))
  = let pm = st.pm in
    let (g', st') = SA.step g st p in
    pages_ok_sw_elim g st;
    assert (run_ok pm p /\ free_ok pm p);
    match (entry pm p).kind with
    | Pool c ->
      pool_unit g st p c;
      assert (span pm p == 1);
      unit_words g g' pm st'.pm p 1 w
    | LargeHead n ->
      run_unit g st p n;
      assert (span pm p == n);
      unit_words g g' pm st'.pm p n w
