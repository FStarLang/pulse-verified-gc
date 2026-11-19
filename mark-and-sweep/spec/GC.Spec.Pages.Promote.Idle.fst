/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Promote.Idle - a minor collection in `Idle`, with pages
/// ---------------------------------------------------------------------------
///
/// Plan §29.1.  The page allocator with a tag is an allocator of
/// `GC.Spec.Pages.Promote` in `Idle` too (`idle_tal`): the invariant is the
/// page `Idle` invariant (`PA.inv I.Idle`), free means blue (`free_stw`),
/// new blocks are white (`I.new_colour I.Idle`).  It meets `contract`
/// (`idle_contract`), by the sweeping instance's lemmas: in `Idle` every
/// page is swept, so the mid-sweep invariant holds (`idle_sw`), what is free
/// mid-sweep is blue (`swept_free`), and the allocator of `Idle` is the one
/// of `Sweeping` (both allocate white).
///
/// The minor collection of `GC.Spec.Pages.Promote` at `idle_tal`
/// (`icollect`) keeps the `Idle` invariant and every block in use, at its
/// size, and makes in use only its copies (`i_facts`), as the one mid-sweep
/// (`GC.Spec.Pages.Promote.Sweep.s_facts`).

module GC.Spec.Pages.Promote.Idle

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Lib.Header
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Promote
open GC.Spec.Pages.Promote.Loop
open GC.Spec.Pages.Promote.Collect

module U64 = FStar.UInt64
module GenInv = GC.Gen.HeapInvariant
module SPI = GC.Spec.SweepPhase.Intrinsic
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module AT = GC.Spec.Pages.AllocTag
module ATO = GC.Spec.Pages.AllocTagOk
module PMP = GC.Spec.Pages.MarkPhase
module MS = GC.Spec.Pages.MidSweep
module MS2 = GC.Spec.Pages.MidSweepStep
module Sc = GC.Spec.Pages.Scrub

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// `Idle` is a mid-sweep state with every page swept
/// ---------------------------------------------------------------------------

/// Every page swept: no word is unswept, so free mid-sweep is blue.
let swept_free (st: pstate) (h: heap) (y: obj_addr)
  : Lemma (requires PMP.all_swept st)
          (ensures not (MS.unswept_at st.pm y) /\ MS.free_sw st.pm h y == free_stw h y)
  = let a = U64.v y - 8 in
    if U64.v zero_addr <= a && a < pages_end then begin
      page_of_spec a;
      MS2.uw_swept st.pm a
    end
    else MS2.uw_out st.pm a

/// **The `Idle` invariant is the mid-sweep one, with every page swept.**
#push-options "--z3rlimit 30"
let idle_sw (g: heap) (st: pstate)
  : Lemma (requires PA.inv I.Idle g st) (ensures MS.pages_ok_sw g st /\ PMP.all_swept st)
  = let pm = st.pm in
    Sc.core_of_ok g st;
    MS.free_sw_ok pm;
    free_stw_ok ();
    wf_with_parts ();
    let same (y: obj_addr) : Lemma (in_use (MS.free_sw pm) g y == in_use free_stw g y)
      = swept_free st g y
    in
    FStar.Classical.forall_intro same;
    let blk (y: obj_addr) : Lemma (SPI.same_block g g (hd_address y)) = () in
    FStar.Classical.forall_intro blk;
    SPI.wf_transport g g free_stw (MS.free_sw pm);
    MS.pages_ok_sw_intro g st
#pop-options

/// ---------------------------------------------------------------------------
/// The allocator in `Idle`
/// ---------------------------------------------------------------------------

let idle_alloc (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t) : GTot (heap & pstate & U64.t) =
  AT.alloc_tag I.Idle g st wz tag

/// The page allocator in `Idle`.
let idle_tal : tal pstate = {
  inv = PA.inv I.Idle;
  alloc = idle_alloc;
  free = free_stw;
  col = White;
}

/// `Idle` and `Sweeping` allocate alike: white.
let idle_is_sweeping (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t)
  : Lemma (AT.alloc_tag I.Idle g st wz tag == AT.alloc_tag I.Sweeping g st wz tag)
  = assert_norm (I.new_colour I.Idle == White);
    assert_norm (I.new_colour I.Sweeping == White)

/// ... and the page state they leave is the one an allocation while
/// marking leaves.
let idle_st (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t)
  : Lemma (let (_, st1, _) = AT.alloc_tag I.Idle g st wz tag in
           let (_, st2, _) = AT.alloc_tag I.Marking g st wz tag in
           st1 == st2)
  = assert_norm (I.new_colour I.Idle == White);
    assert_norm (I.new_colour I.Marking == Black)

/// What the caller may write, mid-sweep with every page swept, is what it
/// may write in `Idle`.
#push-options "--z3rlimit 30"
let idle_written (st: pstate) (g' g'': heap) (x: obj_addr)
  : Lemma (requires PMP.all_swept st /\ AT.fields_written_away free_stw g' g'' x)
          (ensures AT.fields_written_away (MS.free_sw st.pm) g' g'' x)
  = FStar.Classical.forall_intro (swept_free st g'')
#pop-options

#push-options "--z3rlimit 40"
let idle_alloc_ok (g: heap) (st: pstate) (wz: pos) (tag: AT.tag_t)
  : Lemma (requires PA.inv I.Idle g st /\ U64.v tag <> 249)
          (ensures alloc_ok idle_tal g st wz tag)
  = idle_sw g st;
    PMP.mark_inv_of_ok g st;
    ATO.alloc_tag_marking g st wz tag;
    idle_st g st wz tag;
    ATO.alloc_tag_sweeping g st wz tag;
    idle_is_sweeping g st wz tag;
    let (g', st', o) = AT.alloc_tag I.Idle g st wz tag in
    if o <> 0UL then begin
      let x : obj_addr = o in
      is_white_iff x g';
      FStar.Classical.forall_intro (swept_free st g);
      FStar.Classical.forall_intro (swept_free st' g');
      let fill (g'': heap)
        : Lemma (requires AT.fields_written_away free_stw g' g'' x)
                (ensures PA.inv I.Idle g'' st')
        = idle_written st' g' g'' x;
          MS2.sw_end g'' st'
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires fill)
    end
#pop-options

/// The pointer update keeps the `Idle` invariant.
#push-options "--z3rlimit 30"
let idle_update (g: heap) (st: pstate) (upd: obj_addr -> GTot bool) (fwd: forwarding_map)
  : Lemma (requires PA.inv I.Idle g st /\ walk_ok g upd /\ well_formed_heap_with free_stw (update_walk g upd fwd))
          (ensures PA.inv I.Idle (update_walk g upd fwd) st)
  = let g' = update_walk g upd fwd in
    idle_sw g st;
    MS.free_sw_ok st.pm;
    free_stw_ok ();
    FStar.Classical.forall_intro (swept_free st g');
    SPI.well_formed_heap_with_congr free_stw (MS.free_sw st.pm) g';
    ATO.sw_update g st upd fwd;
    MS2.sw_end g' st
#pop-options

/// **The page allocator meets the contract in `Idle`.**
#push-options "--z3rlimit 30"
let idle_contract () : Lemma (contract idle_tal)
  = free_stw_ok ();
    wf_with_parts ();
    let al (g: heap) (st: pstate) (wz: pos) (tag: AT.tag_t)
      : Lemma (PA.inv I.Idle g st /\ U64.v tag <> 249 ==> alloc_ok idle_tal g st wz tag)
      = if FStar.IndefiniteDescription.strong_excluded_middle (PA.inv I.Idle g st /\ U64.v tag <> 249)
        then idle_alloc_ok g st wz tag
    in
    FStar.Classical.forall_intro_4 al;
    let up (g: heap) (st: pstate) (upd: obj_addr -> GTot bool) (fwd: forwarding_map)
      : Lemma (PA.inv I.Idle g st /\ walk_ok g upd /\ well_formed_heap_with free_stw (update_walk g upd fwd) ==>
               PA.inv I.Idle (update_walk g upd fwd) st)
      = if FStar.IndefiniteDescription.strong_excluded_middle
             (PA.inv I.Idle g st /\ walk_ok g upd /\ well_formed_heap_with free_stw (update_walk g upd fwd))
        then idle_update g st upd fwd
    in
    FStar.Classical.forall_intro_4 up
#pop-options

/// ---------------------------------------------------------------------------
/// The minor collection in `Idle`
/// ---------------------------------------------------------------------------

/// **The minor collection in `Idle`**, with the page allocator.
let icollect (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t) : GTot (gresult pstate) =
  collect idle_tal minor g st roots

/// What it starts from: the `Idle` invariant, the nursery's shape, and its
/// major pointers to blocks in use.
let ipre (minor: minor_state) (g: heap) (st: pstate) : prop =
  PA.inv I.Idle g st /\ GenInv.minor_heap_shape minor /\
  GenInv.minor_major_fields_not_free free_stw minor g

/// The blocks a change made: in use after, not before.
let made (g g': heap) (x: obj_addr) : prop =
  in_use free_stw g' x /\ ~(in_use free_stw g x)

/// `since`, and the blocks the collection made.
let with_made (since: obj_addr -> prop) (g g': heap) : obj_addr -> prop =
  fun x -> since x \/ made g g' x

/// **What the collection keeps.**
#push-options "--z3rlimit 30"
let i_facts (minor: minor_state) (g: heap) (st: pstate) (roots: seq U64.t)
  : Lemma (requires ipre minor g st)
          (ensures (let r = icollect minor g st roots in
                    PA.inv I.Idle r.rmajor r.rst /\ r.rminor == minor_reset minor /\
                    (forall (y: obj_addr). in_use free_stw g y ==>
                       in_use free_stw r.rmajor y /\
                       wosize_of_object y r.rmajor == wosize_of_object y g) /\
                    (forall (y: obj_addr). made g r.rmajor y ==> color_of_object y r.rmajor == White)))
  = let a = idle_tal in
    idle_contract ();
    GenInv.minor_heap_shape_elim minor;
    assert (cpre a minor g st);
    collect_inv a minor g st roots;
    let r = icollect minor g st roots in
    let old (y: obj_addr)
      : Lemma (requires in_use free_stw g y)
              (ensures in_use free_stw r.rmajor y /\ wosize_of_object y r.rmajor == wosize_of_object y g)
      = collect_blocks a minor g st roots y;
        wosize_of_object_spec y g;
        wosize_of_object_spec y r.rmajor
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires old);
    let nw (y: obj_addr)
      : Lemma (requires made g r.rmajor y) (ensures color_of_object y r.rmajor == White)
      = collect_blocks a minor g st roots y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires nw)
#pop-options
