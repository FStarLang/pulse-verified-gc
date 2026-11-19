/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.AllocInc - allocation in every phase, in Pulse
/// ---------------------------------------------------------------------------
///
/// Plan §28.  `alloc_ph heap t wz tag marking` is the tagged page allocator
/// (`GC.Impl.Pages.Alloc.alloc_tag`) with the colour rule: black while
/// marking, white otherwise.  From the page invariant of the phase `ph`
/// (`GC.Spec.Pages.Incr.phase_inv`: the `Idle` and `Marking` invariants,
/// and `pages_ok_sw` mid-sweep, whose pages are some swept and some not,
/// told apart in the Pulse state by the sweep epoch) it computes exactly:
///   - the model's tagged allocation of the phase, `AllocTag.alloc_tag ph`,
///     which a minor collection uses for its copies and the page cycle's
///     allocation events with a tag use (`CAllocT`, `CSAllocT`; plan §29.2);
///   - with tag 0, the model's allocation of the phase, `Allocator.alloc ph`,
///     which the page cycle's allocation events with tag 0 use (`CAlloc`,
///     `CSAlloc`);
/// and the new object's colour is the interface's `colour_at`: white in a
/// swept page mid-sweep (`Incr.alloc_tag_phase`).
///
/// The allocator's fast path needs only `Ready.heads_ready`, which each
/// phase's invariant gives (`phase_ready`); mid-sweep from `pages_ok_sw`
/// (`sw_ready`): the class lists hold swept pages only.

module GC.Impl.Pages.AllocInc

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Impl.Heap
open GC.Impl.Pages.State

module U64 = FStar.UInt64
module Hd = GC.Lib.Header
module SO = GC.Spec.Object
module IO = GC.Impl.Object
module I = GC.Spec.AllocIface
module Sh = GC.Spec.Pages.Shape
module B = GC.Spec.Pages.Blocks
module A = GC.Spec.Pages.Alloc
module AP = GC.Spec.Pages.AllocPhase
module AT = GC.Spec.Pages.AllocTag
module PA = GC.Spec.Pages.Allocator
module MS = GC.Spec.Pages.MidSweep
module MSA = GC.Spec.Pages.MidSweepAlloc
module Sc = GC.Spec.Pages.Scrub
module Inc = GC.Spec.Pages.Incr
module Rd = GC.Impl.Pages.Ready
module IA = GC.Impl.Pages.Alloc

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The fast path's facts in every phase
/// ---------------------------------------------------------------------------

/// Mid-sweep: the class lists hold swept pages, with their free slots.
let sw_ready (g: heap) (st: pstate)
  : Lemma (requires MS.pages_ok_sw g st) (ensures Rd.heads_ready st)
  = MS.pages_ok_sw_elim g st;
    let pl (i: nat{i < n_pages}) : Lemma (pool_list_ok g st.pm i)
      = assert (GC.Spec.Pages.Frame.page_local g st.pm i)
    in
    FStar.Classical.forall_intro pl;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (Rd.head_ready_of g st))

let phase_ready (ph: I.phase) (g: heap) (st: pstate)
  : Lemma (requires Inc.phase_inv ph g st) (ensures Rd.heads_ready st)
  = match ph with
    | I.Idle -> Rd.pages_ok_ready g st
    | I.Marking -> Rd.mc_ready g st
    | I.Sweeping -> sw_ready g st

/// ---------------------------------------------------------------------------
/// Tag 0 is the untagged allocator
/// ---------------------------------------------------------------------------

/// A header of tag 0, given a colour and tag 0, is the header recoloured.
let tag0_hdr (h: U64.t) (col: color)
  : Lemma (requires getTag h == 0UL) (ensures AT.tag_hdr h col 0UL == colorHeader h col)
  = all_headers_valid h;
    IO.lib_makeHeader_eq_colorHeader h col;
    IO.getWosize_eq h;
    IO.getTag_eq h;
    IO.makeHeader_eq_pack_header (getWosize h) col (getTag h);
    SO.makeHeader_is_pack_header64 (getWosize h) col (getTag h);
    U64.v_inj (IO.makeHeader (getWosize h) col (getTag h)) (SO.makeHeader (getWosize h) col (getTag h))

/// **With tag 0, the tagged allocator is the coloured one.**
#push-options "--z3rlimit 30"
let alloc_tag_zero (col: color) (g: heap) (st: pstate) (wz: nat)
  : Lemma (AT.alloc_col_tag col 0UL g st wz == AP.alloc_col col g st wz)
  = AT.alloc_col_tag_wz col 0UL g st wz;
    let (g', st', o) = A.alloc g st wz in
    if o <> 0UL && U64.v o >= 8 then begin
      let a = U64.v o - 8 in
      if a < heap_size && a % 8 = 0 then begin
        A.alloc_clears g st wz;
        B.ohdr_spec wz;
        assert (Sh.hdr g' a == B.ohdr wz);
        tag0_hdr (Sh.hdr g' a) col
      end
    end
#pop-options

let new_colour_rule (ph: I.phase) (marking: bool)
  : Lemma (requires marking == I.Marking? ph)
          (ensures (if marking then Hd.Black else Hd.White) == I.new_colour ph)
  = ()

/// ---------------------------------------------------------------------------
/// The allocator of the phase
/// ---------------------------------------------------------------------------

/// **Allocation in phase `ph`** (`marking` says whether it is `Marking`):
/// the model's allocation of the phase, with the tag; with tag 0 the
/// model's allocation event; the new object of the colour `colour_at`.
fn alloc_ph (heap: heap_t) (t: pstate_t) (wz: U64.t) (tag: U64.t{U64.v tag < 256}) (marking: bool)
  (#ph: erased I.phase) (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st ** pure (Inc.phase_inv ph 'g st /\ marking == I.Marking? ph)
  returns o: U64.t
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure ((g', st', o) == AT.alloc_tag ph 'g st (U64.v wz) tag /\
                (tag == 0UL ==> (g', st', o) == PA.alloc ph 'g st (U64.v wz)) /\
                (o == 0UL ==> g' == 'g /\ st' == reveal st) /\
                (o =!= 0UL ==>
                   U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                   color_of_object (o <: obj_addr) g' == I.colour_at MSA.pages_allocator_sw st ph o))
{
  phase_ready ph 'g st;
  Inc.alloc_tag_phase ph 'g st (U64.v wz) tag;
  alloc_tag_zero (I.new_colour ph) 'g st (U64.v wz);
  new_colour_rule ph marking;
  let col : Hd.color_sem = (if marking then Hd.Black else Hd.White);
  IA.alloc_tag heap t wz col tag
}
