/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Incr - the page allocator and sweep in incremental mode
/// ---------------------------------------------------------------------------
///
/// Plan §28.  The specification functions the Pulse code of incremental
/// mode computes, and their facts:
///
///   * **Allocation in every phase** (`alloc_tag_phase`): the tagged
///     allocator in the phase's colour (`AllocTag.alloc_tag ph`), from the
///     phase's page invariant (`MidSweepAlloc.inv_sw`: the `Idle` and
///     `Marking` invariants of `Pages.Allocator`, `pages_ok_sw` mid-sweep),
///     gives the new object the colour of the interface's rule
///     (`I.colour_at`): black while marking, white in a swept page while
///     sweeping, white in `Idle`.
///   * **A slice of the sweep** (`slice_from g st p n`): from page `p`, the
///     model's sweep steps (`SweepAll.step`) one unit after the next, until
///     `n` units have been swept or the pages end.  A unit that is swept
///     already, a free page or a continuation page is passed over and
///     costs nothing, as in the prototype's `incr_step`.  It returns where
///     it stopped, the cursor of the next slice.
///   * **The cursor** (`swept_below pm c`: every page below `c` is swept).
///     A slice keeps it, and so do every other event of the sweep: a sweep
///     step anywhere, an allocation and a program write.  Once the cursor
///     reaches the end of the pages, every page is swept: the sweep may end
///     (`cursor_end`).

module GC.Spec.Pages.Incr

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Seq = FStar.Seq
module I = GC.Spec.AllocIface
module A = GC.Spec.Pages.Alloc
module AP = GC.Spec.Pages.AllocPhase
module AT = GC.Spec.Pages.AllocTag
module PA = GC.Spec.Pages.Allocator
module B = GC.Spec.Pages.Blocks
module SA = GC.Spec.Pages.SweepAll
module MS = GC.Spec.Pages.MidSweep
module MS2 = GC.Spec.Pages.MidSweepStep
module MSA = GC.Spec.Pages.MidSweepAlloc
module PMP = GC.Spec.Pages.MarkPhase

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Allocation in every phase: the colour rule
/// ---------------------------------------------------------------------------

/// The page invariant of each phase: `Idle` and `Marking` as the allocator
/// has them, `pages_ok_sw` mid-sweep.
let phase_inv (ph: I.phase) (g: heap) (st: pstate) : prop = MSA.inv_sw ph g st

/// The tagged allocator's new header has the colour asked for.
let tag_colour (col: color) (tag: AT.tag_t) (g: heap) (st: pstate) (wz: nat)
  : Lemma (let (g', _, o) = AT.alloc_col_tag col tag g st wz in
           o =!= 0UL /\ U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 ==>
           color_of_object (o <: obj_addr) g' == col)
  = let (g1, st1, o) = A.alloc g st wz in
    if o <> 0UL && U64.v o >= 8 && U64.v o < heap_size && U64.v o % 8 = 0 then begin
      let x : obj_addr = o in
      let a = U64.v o - 8 in
      hd_address_spec x;
      let v = AT.tag_hdr (GC.Spec.Pages.Shape.hdr g1 a) col tag in
      B.wr_read g1 a v (hd_address x);
      makeHeader_getColor (getWosize (GC.Spec.Pages.Shape.hdr g1 a)) col tag;
      color_of_object_spec x (B.wr g1 a v)
    end

/// The coloured allocator's new header has the colour asked for.
let recolour_colour (g: heap) (x: obj_addr) (col: color)
  : Lemma (color_of_object x (AP.recolour g (x <: U64.t) col) == col)
  = hd_address_spec x;
    let a = U64.v x - 8 in
    let v = colorHeader (GC.Spec.Pages.Shape.hdr g a) col in
    B.wr_read g a v (hd_address x);
    colorHeader_getColor (GC.Spec.Pages.Shape.hdr g a) col;
    color_of_object_spec x (AP.recolour g (x <: U64.t) col)

/// **The colour rule.**  From the phase's page invariant, the tagged
/// allocator fails with nothing changed, or hands out an object whose colour
/// is the interface's `colour_at`: black while marking, white while
/// sweeping (its header lies in a swept page) and in `Idle`.  Its state and
/// object are the untagged allocator's of the phase (`PA.alloc ph`).
#push-options "--z3rlimit 30"
let alloc_tag_phase (ph: I.phase) (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t)
  : Lemma (requires phase_inv ph g st)
          (ensures (let (g', st', o) = AT.alloc_tag ph g st wz tag in
                    let (g1, st1, o1) = PA.alloc ph g st wz in
                    st' == st1 /\ o == o1 /\
                    (o == 0UL ==> g' == g /\ st' == st) /\
                    (o =!= 0UL ==>
                       U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                       color_of_object (o <: obj_addr) g' == I.colour_at MSA.pages_allocator_sw st ph o)))
  = (match ph with
     | I.Sweeping -> MSA.sweeping_post g st wz
     | _ -> MSA.other_post ph g st wz);
    let (g1, st1, o1) = PA.alloc ph g st wz in
    AT.alloc_col_tag_eq (I.new_colour ph) tag g st wz;
    tag_colour (I.new_colour ph) tag g st wz;
    if o1 <> 0UL then begin
      let x : obj_addr = o1 in
      let (g0, _, _) = A.alloc g st wz in
      recolour_colour g0 x (I.new_colour ph)
    end
#pop-options

/// ---------------------------------------------------------------------------
/// A slice of the sweep
/// ---------------------------------------------------------------------------

/// The step at `p` sweeps a unit: an unswept pool page or run.
let sweeps (pm: page_map) (p: nat{p < n_pages}) : bool =
  not (entry pm p).swept && (Pool? (entry pm p).kind || LargeHead? (entry pm p).kind)

/// **The slice**: from page `p`, sweep steps one unit after the next until
/// `n` units are swept or the pages end; the result and where it stopped.
#push-options "--fuel 1"
let rec slice_from (g: heap) (st: pstate) (p: nat) (n: nat)
  : GTot (heap & pstate & nat) (decreases (if p < n_pages then n_pages - p else 0))
  = if p >= n_pages || n = 0 then (g, st, p)
    else begin
      let k = span st.pm p in
      let n' = if sweeps st.pm p then n - 1 else n in
      let (g', st') = SA.step g st p in
      slice_from g' st' (p + k) n'
    end

let slice_unfold (g: heap) (st: pstate) (p: nat) (n: nat)
  : Lemma (slice_from g st p n ==
           (if p >= n_pages || n = 0 then (g, st, p)
            else begin
              let k = span st.pm p in
              let n' = if sweeps st.pm p then n - 1 else n in
              let (g', st') = SA.step g st p in
              slice_from g' st' (p + k) n'
            end))
  = ()
#pop-options

/// ---------------------------------------------------------------------------
/// The cursor
/// ---------------------------------------------------------------------------

/// Every page below `c` is swept.
let swept_below (pm: page_map) (c: nat) : prop =
  forall (j: nat{j < n_pages}). j < c ==> (entry pm j).swept

/// A continuation page past a swept prefix is swept: its run starts below
/// it, and shares the run's swept bit.
let cont_swept (pm: page_map) (p: nat{p < n_pages})
  : Lemma (requires map_ok pm /\ swept_below pm p /\ ~(walk_page pm p))
          (ensures (entry pm p).swept)
  = assert (cont_ok pm p);
    eliminate exists (h: nat{h < n_pages}). h < p /\ in_run pm h p
    with assert (run_ok pm h)

/// **A step at the cursor** keeps the mid-sweep invariant and moves the
/// cursor past its unit.
let cursor_step (g: heap) (st: pstate) (p: nat{p < n_pages})
  : Lemma (requires MS.pages_ok_sw g st /\ swept_below st.pm p)
          (ensures (let (g', st') = SA.step g st p in
                    MS.pages_ok_sw g' st' /\ p + span st.pm p <= n_pages /\
                    swept_below st'.pm (p + span st.pm p)))
  = MS.pages_ok_sw_elim g st;
    MS2.step_sw g st p;
    let pm = st.pm in
    assert (run_ok pm p);
    if not (walk_page pm p) then cont_swept pm p

/// **The slice** keeps the mid-sweep invariant and the cursor, and moves
/// the cursor forward.
#push-options "--fuel 1"
let rec slice_ok (g: heap) (st: pstate) (p: nat) (n: nat)
  : Lemma (requires MS.pages_ok_sw g st /\ swept_below st.pm p)
          (ensures (let (g', st', p') = slice_from g st p n in
                    MS.pages_ok_sw g' st' /\ swept_below st'.pm p' /\ p <= p'))
          (decreases (if p < n_pages then n_pages - p else 0))
  = if p >= n_pages || n = 0 then ()
    else begin
      cursor_step g st p;
      let k = span st.pm p in
      let n' = if sweeps st.pm p then n - 1 else n in
      let (g', st') = SA.step g st p in
      slice_ok g' st' (p + k) n'
    end
#pop-options

/// A sweep step anywhere unsweeps nothing.
let step_cursor (g: heap) (st: pstate) (p: nat{p < n_pages}) (c: nat)
  : Lemma (requires MS.pages_ok_sw g st /\ swept_below st.pm c)
          (ensures swept_below (snd (SA.step g st p)).pm c)
  = MS2.step_sw g st p

/// An allocation, with any colour and tag, unsweeps nothing.
let alloc_cursor (col: color) (tag: AT.tag_t) (g: heap) (st: pstate) (wz: nat) (c: nat)
  : Lemma (requires map_ok st.pm /\ swept_below st.pm c)
          (ensures (let (_, st', _) = AT.alloc_col_tag col tag g st wz in swept_below st'.pm c))
  = MS.alloc_same g st wz

/// The sweep's start leaves the cursor at 0; at the end of the pages,
/// every page is swept: the sweep may end.
let cursor_start (pm: page_map) : Lemma (swept_below pm 0) = ()

let cursor_end (st: pstate) (c: nat)
  : Lemma (requires swept_below st.pm c /\ c >= n_pages) (ensures PMP.all_swept st)
  = ()

/// A budget of a unit per page left reaches the end of the pages.
#push-options "--fuel 1"
let rec slice_full (g: heap) (st: pstate) (p: nat) (n: nat)
  : Lemma (requires p + n >= n_pages)
          (ensures (let (_, _, p') = slice_from g st p n in p' >= n_pages))
          (decreases (if p < n_pages then n_pages - p else 0))
  = if p >= n_pages || n = 0 then ()
    else begin
      let k = span st.pm p in
      let n' = if sweeps st.pm p then n - 1 else n in
      let (g', st') = SA.step g st p in
      slice_full g' st' (p + k) n'
    end
#pop-options
