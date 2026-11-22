/// ---------------------------------------------------------------------------
/// GC.Spec.Top.PagesStep - one step of the page sweep meets the sweep
/// contract
/// ---------------------------------------------------------------------------
///
/// `PagesSweep.pstep` sweeps the next unit (an unswept pool page or large
/// run) at or after the cursor.  Clause by clause (`Iface.sweep_step_post`),
/// on the readings `cabs g` before and `cabs g'` after:
///   - the region the step swept is the unit's words (`region_iff`), which
///     were unswept; the unswept set only shrinks (`progress`);
///   - the blocks in use after are those before but the white ones of the
///     unit (`PagesFree.step_frees_white`); a black one is whitened in place;
///     outside the unit nothing changes (`kept_out`);
///   - word by word, the free words after are those before and those of the
///     white blocks of the unit (`PagesFree.step_frees_words`);
///   - `freed_words`, counted on the byte heap over the objects of the walk,
///     is the model's sum over addresses (GC.Spec.Top.PagesFreed);
///   - the mid-sweep invariant, and the cursor, again (`Incr.cursor_step`).

module GC.Spec.Top.PagesStep

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
open GC.Spec.Top.Word
open GC.Spec.Top.Abs
open GC.Spec.Top.Low
open GC.Spec.Top.ByteFacts
open GC.Spec.Top.ByteWrite
open GC.Spec.Top.ByteRep
open GC.Spec.Top.PagesAlloc
open GC.Spec.Top.PagesAllocOk
open GC.Spec.Top.PagesInst
open GC.Spec.Top.PagesSweep
open GC.Spec.Top.PagesFrame
module M = GC.Spec.Top.Heap
module R = GC.Spec.Top.Rep
module T = GC.Spec.Top.Iface
module U64 = FStar.UInt64
module Seq = FStar.Seq
module G = GC.Spec.Pages.Graft
module PMP = GC.Spec.Pages.MarkPhase
module MS = GC.Spec.Pages.MidSweep
module MS2 = GC.Spec.Pages.MidSweepStep
module SA = GC.Spec.Pages.SweepAll
module Incr = GC.Spec.Pages.Incr
module PF = GC.Spec.Top.PagesFree
module Rp = GC.Spec.Pages.Replace
module CS = GC.Spec.Pages.Cycle.State
module SU = GC.Spec.Pages.SweepUnits
module Th = GC.Spec.Pages.Theorems

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The next unit
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec nextu_spec (pm: page_map) (c: nat)
  : Lemma (ensures (let q = nextu pm c in
                    (q < n_pages ==> c <= q /\ Incr.sweeps pm q) /\
                    (forall (j: nat{j < n_pages}). c <= j /\ j < q ==> not (Incr.sweeps pm j))))
          (decreases (if c < n_pages then n_pages - c else 0))
  = if c >= n_pages then () else if Incr.sweeps pm c then () else nextu_spec pm (c + 1)
#pop-options

/// A page the sweep passes over, past a swept prefix, is swept.
let pass_swept (pm: page_map) (c: nat{c < n_pages})
  : Lemma (requires map_ok pm /\ Incr.swept_below pm c /\ not (Incr.sweeps pm c))
          (ensures Incr.swept_below pm (c + 1))
  = if walk_page pm c then assert (free_ok pm c)
    else Incr.cont_swept pm c

#push-options "--fuel 1"
let rec nextu_found (pm: page_map) (c: nat)
  : Lemma (requires map_ok pm /\ Incr.swept_below pm c /\ ~(forall (i: nat{i < n_pages}). (entry pm i).swept))
          (ensures nextu pm c < n_pages /\ Incr.swept_below pm (nextu pm c))
          (decreases (if c < n_pages then n_pages - c else 0))
  = if c >= n_pages then ()
    else if Incr.sweeps pm c then ()
    else begin
      pass_swept pm c;
      nextu_found pm (c + 1)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// The unit swept
/// ---------------------------------------------------------------------------

/// The unit at a page the sweep visits: its facts (`MidSweepStep.swept_unit`).
let unit_facts (g: heap) (st: pstate) (q: nat{q < n_pages})
  : Lemma (requires MS.pages_ok_sw g st /\ Incr.sweeps st.pm q)
          (ensures (let (g', st') = SA.step g st q in
                    MS2.swept_unit g g' st.pm st'.pm q (span st.pm q) /\
                    MS.pages_ok_sw g' st' /\ q + span st.pm q <= n_pages))
  = MS2.step_sw g st q;
    MS.pages_ok_sw_elim g st;
    let pm = st.pm in
    assert (run_ok pm q);
    match (entry pm q).kind with
    | Pool c -> PF.pool_unit g st q c
    | LargeHead n -> PF.run_unit g st q n

/// A model word is in the unit.
let in_u (q k: nat) (o: nat) : bool = page_base q <= pos o && pos o < page_base (q + k)

/// The region the step swept is the unit.
let region_iff (pm pm': page_map) (g g': heap) (q k: nat) (o: nat)
  : Lemma (requires MS2.swept_unit g g' pm pm' q k)
          (ensures (G.uw pm (pos o) && not (G.uw pm' (pos o))) == in_u q k o /\
                   (G.uw pm' (pos o) ==> G.uw pm (pos o)))
  = ()

/// ---------------------------------------------------------------------------
/// Blocks
/// ---------------------------------------------------------------------------

/// Fields read from equal words.
let field_same (g g': heap) (o: nat)
  : Lemma (requires M.is_block (cabs g) o /\ (cabs g').M.hd o == (cabs g).M.hd o /\
                    (forall (i: nat). i < M.wz_of (cabs g) o ==> word g' (o + 1 + i) == word g (o + 1 + i)))
          (ensures forall (i: nat). i < M.wz_of (cabs g) o ==> M.field (cabs g') o i == M.field (cabs g) o i)
  = let f (i: nat) : Lemma (i < M.wz_of (cabs g) o ==> M.field (cabs g') o i == M.field (cabs g) o i)
      = if i < M.wz_of (cabs g) o then begin
          let w = o + 1 + i in
          assert (M.covers (abs g) o w /\ M.covers (abs g') o w);
          is_fw_iff g w; is_fw_iff g' w
        end in
    FStar.Classical.forall_intro f

/// In use after: in use before, and not a white block of the unit.
#push-options "--z3rlimit 40"
let use_after (g: heap) (st: pstate) (q: nat{q < n_pages}) (o: nat)
  : Lemma (requires MS.pages_ok_sw g st /\ Incr.sweeps st.pm q)
          (ensures (let (g', _) = SA.step g st q in
                    used (cabs g') o <==>
                    (used (cabs g) o /\ ~(in_u q (span st.pm q) o /\ M.col_of (cabs g) o == M.White))))
  = let (g', st') = SA.step g st q in
    used_iff g o; used_iff g' o;
    if pos o + 8 < heap_size then begin
      let y = obj_of o in
      PF.step_frees_white g st q y;
      obj_of_v o;
      if Seq.mem y (objects zero_addr g) then begin
        obj_maddr g y; maddr_obj o;
        abs_header g o;
        is_white_iff y g
      end
    end
#pop-options

/// The word a block's header is at, on the walk from a unit's start.
let unit_walk_to (g: heap) (s e: nat) (o: nat)
  : Lemma (requires steps_to g Rp.z s /\ pos o + 8 < heap_size /\ Seq.mem (obj_of o) (objects zero_addr g) /\
                    s <= pos o)
          (ensures steps_to g s (pos o))
  = obj_of_v o;
    Rp.obj_iff g (obj_of o);
    Rp.steps_to_det g Rp.z s (pos o)

/// A black block of the unit: whitened in place.
#push-options "--z3rlimit 40"
let black_kept (g: heap) (st: pstate) (q: nat{q < n_pages}) (o: nat)
  : Lemma (requires MS.pages_ok_sw g st /\ Incr.sweeps st.pm q /\ used (cabs g) o /\
                    in_u q (span st.pm q) o /\ M.col_of (cabs g) o == M.Black)
          (ensures (let (g', _) = SA.step g st q in
                    used (cabs g') o /\ M.col_of (cabs g') o == M.White /\ M.same_contents (cabs g) (cabs g') o))
  = let (g', st') = SA.step g st q in
    unit_facts g st q;
    let k = span st.pm q in
    let s = page_base q in
    let e = page_base (q + k) in
    used_iff g o;
    let y = obj_of o in
    obj_of_v o;
    Rp.hdr_obj g y;
    abs_header g o;
    is_black_iff y g;
    assert (color_at g (pos o) == Black);
    unit_walk_to g s e o;
    assert (SU.unit_ok g g' q k);
    assert (steps_to g' s (pos o) /\ Th.whitened_at g g' (pos o));
    MS2.whitened_colour g g' (pos o);
    MS2.unit_walk g g' s e s;
    steps_to_le g' s e;
    steps_to_trans g' Rp.z s (pos o);
    Rp.block_before g' s (pos o) e;
    Rp.obj_iff g' y;
    Rp.hdr_obj g' y;
    hd_of_obj o;
    assert (word g' o == colorHeader (word g o) White);
    colorHeader_abs (word g o) White;
    obj_maddr g' y; maddr_obj o;
    abs_header g' o;
    is_blue_iff y g';
    used_iff g' o;
    let wd (i: nat) : Lemma (i < M.wz_of (cabs g) o ==> word g' (o + 1 + i) == word g (o + 1 + i))
      = if i < M.wz_of (cabs g) o then begin
          msize_pos (o + 1 + i);
          pos_aligned (o + 1 + i)
        end in
    FStar.Classical.forall_intro wd;
    let fld (i: nat) : Lemma (i < M.wz_of (cabs g) o ==> M.field (cabs g') o i == M.field (cabs g) o i)
      = if i < M.wz_of (cabs g) o then begin
          let w = o + 1 + i in
          assert (M.covers (abs g) o w /\ M.covers (abs g') o w);
          is_fw_iff g w; is_fw_iff g' w
        end in
    FStar.Classical.forall_intro fld
#pop-options

/// Outside the unit, every block keeps its place, header and fields.
#push-options "--z3rlimit 40"
let kept_out (g: heap) (st: pstate) (q: nat{q < n_pages}) (o: nat)
  : Lemma (requires MS.pages_ok_sw g st /\ Incr.sweeps st.pm q /\ M.is_block (cabs g) o /\
                    ~(in_u q (span st.pm q) o))
          (ensures (let (g', _) = SA.step g st q in
                    (cabs g').M.hd o == (cabs g).M.hd o /\
                    (forall (i: nat). i < M.wz_of (cabs g) o ==> M.field (cabs g') o i == M.field (cabs g) o i)))
  = let (g', st') = SA.step g st q in
    unit_facts g st q;
    let k = span st.pm q in
    let s = page_base q in
    let e = page_base (q + k) in
    mblock (cabs g) g o;
    let y = obj_of o in
    obj_of_v o;
    MS2.unit_obj_out g g' s e y;
    abs_is_block g' o;
    hd_of_obj o;
    Rp.hdr_obj g y;
    abs_header g o;
    let wd (i: nat) : Lemma (i < M.wz_of (cabs g) o ==> word g' (o + 1 + i) == word g (o + 1 + i))
      = if i < M.wz_of (cabs g) o then begin
          msize_pos (o + 1 + i);
          pos_aligned (o + 1 + i)
        end in
    FStar.Classical.forall_intro wd;
    msize_pos o;
    pos_aligned o;
    hp_v o;
    assert (U64.v (hp o) == U64.v y - 8);
    assert (read_word g' (hp o) == read_word g (hp o));
    field_same g g' o
#pop-options

/// ---------------------------------------------------------------------------
/// Words
/// ---------------------------------------------------------------------------

/// A unit: walk positions `s` (reached) and `e` (from `s`), in the pages.
let unit_ok_walk (g: heap) (s e: nat) : prop =
  steps_to g Rp.z s /\ steps_to g s e /\ s >= base /\ e + 16 <= heap_size

/// A model block covering a word of the unit lies in the unit.
#push-options "--z3rlimit 40"
let block_in_unit (g: heap) (s e: nat) (o w: nat)
  : Lemma (requires unit_ok_walk g s e /\ M.covers (abs g) o w /\ s <= pos w /\ pos w < e)
          (ensures s <= pos o /\ pos o < e /\ pos o + 8 * (M.wz_of (abs g) o + 1) <= e /\
                   steps_to g s (pos o))
  = abs_is_block g o;
    abs_header g o;
    let y = obj_of o in
    obj_of_v o;
    Rp.obj_iff g y;
    Rp.hdr_obj g y;
    steps_to_le g s e;
    steps_to_trans g Rp.z s e;
    if pos o < s then Rp.block_before g Rp.z (pos o) s
    else begin
      Rp.steps_to_det g Rp.z s (pos o);
      Rp.block_before g s (pos o) e
    end
#pop-options

/// The block the page walk of a unit has at a byte, as a model block.
#push-options "--z3rlimit 40"
let covering_block (g: heap) (s e: nat) (b w: nat)
  : Lemma (requires unit_ok_walk g s e /\ PF.covering g s e b (pos w))
          (ensures b >= base /\ pos (mpos b) == b /\ M.covers (abs g) (mpos b) w /\
                   M.is_block (abs g) (mpos b) /\
                   abs_col (color_at g b) == M.col_of (abs g) (mpos b))
  = steps_to_le g s b;
    steps_to_trans g Rp.z s b;
    Rp.block_before g s b e;
    base_facts ();
    let o = mpos b in
    assert (b % 8 == 0);
    FStar.Math.Lemmas.lemma_div_exact (b - base) 8;
    assert (pos o == b);
    let y = obj_of o in
    obj_of_v o;
    Rp.obj_iff g y;
    Rp.hdr_obj g y;
    abs_is_block g o;
    abs_header g o
#pop-options

/// A byte of the unit covered by a block of a colour (`PagesFree.covered_by`),
/// read in the model.
let covered_iff (g: heap) (s e: nat) (w: nat) (ok: color_sem -> bool)
  : Lemma (requires unit_ok_walk g s e /\ s <= pos w /\ pos w < e)
          (ensures PF.covered_by g s e (pos w) ok <==>
                   (exists (o: nat). M.covers (abs g) o w /\ ok (col_sem (M.col_of (abs g) o))))
  = let fwd (b: nat) : Lemma (requires PF.covering g s e b (pos w) /\ ok (color_at g b))
                              (ensures exists (o: nat). M.covers (abs g) o w /\ ok (col_sem (M.col_of (abs g) o)))
      = covering_block g s e b w in
    let bwd (o: nat) : Lemma (requires M.covers (abs g) o w /\ ok (col_sem (M.col_of (abs g) o)))
                              (ensures PF.covered_by g s e (pos w) ok)
      = block_in_unit g s e o w;
        let y = obj_of o in
        obj_of_v o;
        abs_is_block g o;
        abs_header g o;
        Rp.hdr_obj g y;
        assert (PF.covering g s e (pos o) (pos w)) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fwd);
    FStar.Classical.forall_intro (FStar.Classical.move_requires bwd)

/// The unit's walk, before and after.
let unit_walks (g: heap) (st: pstate) (q: nat{q < n_pages})
  : Lemma (requires MS.pages_ok_sw g st /\ Incr.sweeps st.pm q)
          (ensures (let (g', _) = SA.step g st q in
                    let k = span st.pm q in
                    unit_ok_walk g (page_base q) (page_base (q + k)) /\
                    unit_ok_walk g' (page_base q) (page_base (q + k))))
  = unit_facts g st q;
    let (g', st') = SA.step g st q in
    let k = span st.pm q in
    MS2.unit_walk g g' (page_base q) (page_base (q + k)) (page_base q);
    page_base_mono q (q + k);
    page_base_mono 0 q;
    pages_end_bound ()

/// A free word: covered by a blue block.
let fw (g: heap) (w: nat) : prop =
  exists (o: nat). M.covers (cabs g) o w /\ M.col_of (cabs g) o == M.Blue

/// A word the step frees: covered by a white block of the unit.
let ww (g: heap) (q k: nat) (w: nat) : prop =
  exists (o: nat). M.covers (cabs g) o w /\ used (cabs g) o /\ in_u q k o /\ M.col_of (cabs g) o == M.White

/// Outside the unit, a block covering a word is the same block on both sides.
#push-options "--z3rlimit 40"
let out_cover (g g': heap) (s e: nat) (o w: nat)
  : Lemma (requires MS2.unit_step g g' s e /\ unit_ok_walk g' s e /\ unit_ok_walk g s e /\
                    M.covers (abs g') o w /\ (pos w < s \/ pos w >= e))
          (ensures M.covers (abs g) o w /\ M.col_of (abs g) o == M.col_of (abs g') o)
  = abs_is_block g' o;
    if s <= pos o && pos o < e then begin
      abs_header g' o;
      let y = obj_of o in
      obj_of_v o;
      Rp.obj_iff g' y; Rp.hdr_obj g' y;
      Rp.steps_to_det g' Rp.z s (pos o);
      Rp.block_before g' s (pos o) e
    end
    else begin
      let y = obj_of o in
      obj_of_v o;
      MS2.unit_obj_out g g' s e y;
      abs_is_block g o;
      Rp.hdr_obj g y; Rp.hdr_obj g' y;
      hd_of_obj o;
      msize_pos o; pos_aligned o; hp_v o;
      Rp.obj_iff g y;
      assert (read_word g' (hp o) == read_word g (hp o))
    end

let out_cover_back (g g': heap) (s e: nat) (o w: nat)
  : Lemma (requires MS2.unit_step g g' s e /\ unit_ok_walk g s e /\
                    M.covers (abs g) o w /\ (pos w < s \/ pos w >= e))
          (ensures M.covers (abs g') o w /\ M.col_of (abs g) o == M.col_of (abs g') o)
  = abs_is_block g o;
    if s <= pos o && pos o < e then begin
      abs_header g o;
      let y = obj_of o in
      obj_of_v o;
      Rp.obj_iff g y; Rp.hdr_obj g y;
      Rp.steps_to_det g Rp.z s (pos o);
      Rp.block_before g s (pos o) e
    end
    else begin
      let y = obj_of o in
      obj_of_v o;
      MS2.unit_obj_out g g' s e y;
      abs_is_block g' o;
      Rp.hdr_obj g y;
      hd_of_obj o;
      msize_pos o; pos_aligned o; hp_v o;
      assert (read_word g' (hp o) == read_word g (hp o))
    end
#pop-options

/// A block of the unit covers words of the unit only.
let unit_block_cover (g: heap) (s e: nat) (o w: nat)
  : Lemma (requires unit_ok_walk g s e /\ M.covers (abs g) o w /\ s <= pos o /\ pos o < e)
          (ensures s <= pos w /\ pos w < e)
  = abs_is_block g o;
    abs_header g o;
    let y = obj_of o in
    obj_of_v o;
    Rp.obj_iff g y; Rp.hdr_obj g y;
    Rp.steps_to_det g Rp.z s (pos o);
    Rp.block_before g s (pos o) e

/// Free words, as the page modules count them on a unit.
let fw_cov (g: heap) (s e: nat) (w: nat)
  : Lemma (requires unit_ok_walk g s e /\ s <= pos w /\ pos w < e)
          (ensures fw g w <==> PF.covered_by g s e (pos w) PF.is_blue_c)
  = covered_iff g s e w PF.is_blue_c

let ffw_cov (g: heap) (q k: nat) (w: nat)
  : Lemma (requires unit_ok_walk g (page_base q) (page_base (q + k)) /\
                    page_base q <= pos w /\ pos w < page_base (q + k))
          (ensures (fw g w \/ ww g q k w) <==> PF.covered_by g (page_base q) (page_base (q + k)) (pos w) PF.is_free_or_freed)
  = let s = page_base q in
    let e = page_base (q + k) in
    covered_iff g s e w PF.is_free_or_freed;
    let wh (o: nat) : Lemma (M.covers (abs g) o w /\ M.col_of (abs g) o == M.White ==> used (cabs g) o /\ in_u q k o)
      = if M.covers (abs g) o w && M.col_of (abs g) o = M.White then block_in_unit g s e o w in
    FStar.Classical.forall_intro wh

/// **Free words grow exactly** by the words of the unit's white blocks.
#push-options "--z3rlimit 40"
let words_step (g: heap) (st: pstate) (q: nat{q < n_pages}) (w: nat)
  : Lemma (requires MS.pages_ok_sw g st /\ Incr.sweeps st.pm q)
          (ensures (let (g', _) = SA.step g st q in
                    fw g' w <==> (fw g w \/ ww g q (span st.pm q) w)))
  = let (g', st') = SA.step g st q in
    unit_facts g st q;
    unit_walks g st q;
    let k = span st.pm q in
    let s = page_base q in
    let e = page_base (q + k) in
    if s <= pos w && pos w < e then begin
      fw_cov g' s e w;
      PF.step_frees_words g st q (pos w);
      ffw_cov g q k w
    end
    else begin
      let a (o: nat) : Lemma (M.covers (abs g') o w ==> M.covers (abs g) o w /\ M.col_of (abs g) o == M.col_of (abs g') o)
        = if M.covers (abs g') o w then out_cover g g' s e o w in
      FStar.Classical.forall_intro a;
      let b (o: nat) : Lemma (M.covers (abs g) o w ==> M.covers (abs g') o w /\ M.col_of (abs g) o == M.col_of (abs g') o)
        = if M.covers (abs g) o w then out_cover_back g g' s e o w in
      FStar.Classical.forall_intro b;
      let nw (o: nat) : Lemma (~(M.covers (abs g) o w /\ in_u q k o))
        = if M.covers (abs g) o w && in_u q k o then unit_block_cover g s e o w in
      FStar.Classical.forall_intro nw
    end
#pop-options
