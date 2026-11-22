/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.PromoteInst - the page allocator meets the promotion contract
/// ---------------------------------------------------------------------------
///
/// Plan §27.3.  The page allocator with a tag (`AT.alloc_tag`) is an
/// allocator of `GC.Spec.Pages.Promote` (`tal pstate`), and meets
/// `contract`:
///
///   * while marking (`mark_tal`): the invariant is the page `Marking`
///     invariant (`PMP.mark_inv`), free means blue, new blocks are black;
///   * while sweeping (`sw_tal pm0`): the invariant is the mid-sweep one
///     (`MS.pages_ok_sw`) with the unswept pages of `pm0`, which an
///     allocation keeps; free means `MS.free_sw pm0` (blue, or white in an
///     unswept page), new blocks are white (they lie in swept pages).
///
/// The allocation facts are `GC.Spec.Pages.AllocTagOk`'s; the pointer
/// update keeps the invariant by `mark_inv_update` and `sw_update`.

module GC.Spec.Pages.PromoteInst

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Lib.Header
open GC.Spec.Fields
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Gen.Promote
open GC.Spec.Pages.Promote

module U64 = FStar.UInt64
module I = GC.Spec.AllocIface
module AT = GC.Spec.Pages.AllocTag
module ATO = GC.Spec.Pages.AllocTagOk
module PMP = GC.Spec.Pages.MarkPhase
module MS = GC.Spec.Pages.MidSweep
module SPI = GC.Spec.SweepPhase.Intrinsic

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// While marking
/// ---------------------------------------------------------------------------

let mark_alloc (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t) : GTot (heap & pstate & U64.t) =
  AT.alloc_tag I.Marking g st wz tag

/// The page allocator while marking.
let mark_tal : tal pstate = {
  inv = PMP.mark_inv;
  alloc = mark_alloc;
  free = free_stw;
  col = (fun _ -> Black);
}

#push-options "--z3rlimit 30"
let mark_alloc_ok (g: heap) (st: pstate) (wz: pos) (tag: AT.tag_t)
  : Lemma (requires PMP.mark_inv g st /\ U64.v tag <> 249)
          (ensures alloc_ok mark_tal g st wz tag)
  = ATO.alloc_tag_marking g st wz tag;
    let (g', st', o) = AT.alloc_tag I.Marking g st wz tag in
    if o <> 0UL then begin
      let x : obj_addr = o in
      is_black_iff x g'
    end
#pop-options

/// **The page allocator meets the contract while marking.**
let mark_contract () : Lemma (contract mark_tal)
  = free_stw_ok ();
    let al (g: heap) (st: pstate) (wz: pos) (tag: AT.tag_t)
      : Lemma (PMP.mark_inv g st /\ U64.v tag <> 249 ==> alloc_ok mark_tal g st wz tag)
      = if FStar.IndefiniteDescription.strong_excluded_middle (PMP.mark_inv g st /\ U64.v tag <> 249)
        then mark_alloc_ok g st wz tag
    in
    FStar.Classical.forall_intro_4 al;
    let up (g: heap) (st: pstate) (upd: obj_addr -> GTot bool) (fwd: forwarding_map)
      : Lemma (PMP.mark_inv g st /\ walk_ok g upd /\ well_formed_heap_with free_stw (update_walk g upd fwd) ==>
               PMP.mark_inv (update_walk g upd fwd) st)
      = if FStar.IndefiniteDescription.strong_excluded_middle
             (PMP.mark_inv g st /\ walk_ok g upd /\ well_formed_heap_with free_stw (update_walk g upd fwd))
        then ATO.mark_inv_update g st upd fwd
    in
    FStar.Classical.forall_intro_4 up

/// ---------------------------------------------------------------------------
/// While sweeping
/// ---------------------------------------------------------------------------

let sw_alloc (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t) : GTot (heap & pstate & U64.t) =
  AT.alloc_tag I.Sweeping g st wz tag

/// The mid-sweep invariant, with the unswept pages of `pm0`.
let sw_inv (pm0: page_map) (g: heap) (st: pstate) : prop =
  MS.pages_ok_sw g st /\ (forall (y: obj_addr). MS.unswept_at st.pm y == MS.unswept_at pm0 y)

/// The page allocator while sweeping.
let sw_tal (pm0: page_map) : tal pstate = {
  inv = sw_inv pm0;
  alloc = sw_alloc;
  free = MS.free_sw pm0;
  col = (fun _ -> White);
}

/// Page maps with the same unswept pages have the same blocks in use.
let sw_in_use (pm pm': page_map) (g: heap) (y: obj_addr)
  : Lemma (requires forall (z: obj_addr). MS.unswept_at pm' z == MS.unswept_at pm z)
          (ensures in_use (MS.free_sw pm') g y == in_use (MS.free_sw pm) g y)
  = ()

let sw_wf (pm pm': page_map) (g: heap)
  : Lemma (requires forall (z: obj_addr). MS.unswept_at pm' z == MS.unswept_at pm z)
          (ensures well_formed_heap_with (MS.free_sw pm') g <==> well_formed_heap_with (MS.free_sw pm) g)
  = FStar.Classical.forall_intro (sw_in_use pm pm' g);
    SPI.well_formed_heap_with_congr (MS.free_sw pm) (MS.free_sw pm') g

/// What the caller may write, at two page maps with the same unswept pages.
#push-options "--z3rlimit 30"
let sw_written (pm pm': page_map) (g' g'': heap) (x: obj_addr)
  : Lemma (requires (forall (z: obj_addr). MS.unswept_at pm' z == MS.unswept_at pm z) /\
                    AT.fields_written_away (MS.free_sw pm) g' g'' x)
          (ensures AT.fields_written_away (MS.free_sw pm') g' g'' x)
  = FStar.Classical.forall_intro (sw_in_use pm pm' g'')
#pop-options

#push-options "--z3rlimit 40"
let sw_alloc_ok (pm0: page_map) (g: heap) (st: pstate) (wz: pos) (tag: AT.tag_t)
  : Lemma (requires sw_inv pm0 g st /\ U64.v tag <> 249)
          (ensures alloc_ok (sw_tal pm0) g st wz tag)
  = ATO.alloc_tag_sweeping g st wz tag;
    let (g', st', o) = AT.alloc_tag I.Sweeping g st wz tag in
    if o <> 0UL then begin
      let x : obj_addr = o in
      is_white_iff x g';
      FStar.Classical.forall_intro (sw_in_use st.pm pm0 g);
      FStar.Classical.forall_intro (sw_in_use st'.pm pm0 g');
      let fill (g'': heap)
        : Lemma (requires AT.fields_written_away (MS.free_sw pm0) g' g'' x)
                (ensures sw_inv pm0 g'' st')
        = sw_written pm0 st'.pm g' g'' x
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires fill)
    end
#pop-options

/// **The page allocator meets the contract while sweeping.**
#push-options "--z3rlimit 30"
let sw_contract (pm0: page_map) : Lemma (contract (sw_tal pm0))
  = MS.free_sw_ok pm0;
    let wf (g: heap) (st: pstate)
      : Lemma (sw_inv pm0 g st ==> well_formed_heap_with (MS.free_sw pm0) g)
      = if FStar.IndefiniteDescription.strong_excluded_middle (sw_inv pm0 g st) then begin
          MS.pages_ok_sw_elim g st;
          sw_wf st.pm pm0 g
        end
    in
    FStar.Classical.forall_intro_2 wf;
    let al (g: heap) (st: pstate) (wz: pos) (tag: AT.tag_t)
      : Lemma (sw_inv pm0 g st /\ U64.v tag <> 249 ==> alloc_ok (sw_tal pm0) g st wz tag)
      = if FStar.IndefiniteDescription.strong_excluded_middle (sw_inv pm0 g st /\ U64.v tag <> 249)
        then sw_alloc_ok pm0 g st wz tag
    in
    FStar.Classical.forall_intro_4 al;
    let up (g: heap) (st: pstate) (upd: obj_addr -> GTot bool) (fwd: forwarding_map)
      : Lemma (sw_inv pm0 g st /\ walk_ok g upd /\ well_formed_heap_with (MS.free_sw pm0) (update_walk g upd fwd) ==>
               sw_inv pm0 (update_walk g upd fwd) st)
      = if FStar.IndefiniteDescription.strong_excluded_middle
             (sw_inv pm0 g st /\ walk_ok g upd /\ well_formed_heap_with (MS.free_sw pm0) (update_walk g upd fwd))
        then begin
          sw_wf st.pm pm0 (update_walk g upd fwd);
          ATO.sw_update g st upd fwd
        end
    in
    FStar.Classical.forall_intro_4 up
#pop-options
