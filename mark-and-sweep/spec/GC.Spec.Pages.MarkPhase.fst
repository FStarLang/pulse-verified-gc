/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.MarkPhase - the allocator's invariant while the collector marks
/// ---------------------------------------------------------------------------
///
/// While a collector marks, every page is swept: the sweep of the previous
/// cycle has finished, and the allocator only makes swept pages.  The
/// allocator's invariant for that phase is `mark_inv`: `pages_ok` up to the
/// colours of live objects (`GC.Spec.Pages.AllocPhase.pages_ok_mc`), with
/// every page swept.
///
///   - `mark_inv_of_ok`: `pages_ok`, `well_formed_heap` and every page swept
///     give it, which is the state `sweep_all` ends in.
///   - `mark_inv_recolour`: it survives recolouring a live object any colour
///     but blue, which is all a mark does to the heap.
///   - `mark_inv_alloc`: a black allocation keeps it.

module GC.Spec.Pages.MarkPhase

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
open GC.Spec.Pages.Blocks
open GC.Spec.Pages.Theorems
open GC.Spec.Pages.Recolour
open GC.Spec.Pages.ColourFacts
open GC.Spec.Pages.AllocPhase

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module HE = GC.Gen.HeapExtensional
module A = GC.Spec.Pages.Alloc
module R = GC.Spec.Pages.Replace
module SU = GC.Spec.Pages.SweepUnits
module SA = GC.Spec.Pages.SweepAll
module Pool = GC.Spec.Pages.Pool
module LG = GC.Spec.Pages.Large
module NR = GC.Spec.Pages.NewRun
module PI = GC.Spec.Pages.PoolInit

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

let all_swept (st: pstate) : prop =
  forall (i: nat{i < n_pages}). (entry st.pm i).swept == true

let mark_inv (g: heap) (st: pstate) : prop = pages_ok_mc g st /\ all_swept st

let mark_inv_of_ok (g: heap) (st: pstate)
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ all_swept st) (ensures mark_inv g st)
  = mc_of_ok g st

/// ---------------------------------------------------------------------------
/// A live object in a swept page is white
/// ---------------------------------------------------------------------------

/// A free page is one block.
let free_page_only (g: heap) (i: nat{i < n_pages}) (h: nat)
  : Lemma (requires free_page_shape g i /\ steps_to g (page_base i) h /\ h < page_base (i + 1))
          (ensures h == page_base i)
  = page_base_mono i (i + 1);
    steps_to_le g (page_base i) h;
    if h > page_base i then begin
      steps_to_refl g (page_base i);
      R.block_before g (page_base i) (page_base i) h;
      FStar.Math.Lemmas.distributivity_add_left i 1 page_bytes
    end

let slot0 (i: nat) (c: nat{c < n_cls}) : Lemma (slot_base i c 0 == page_base i) = ()

let live_white (g: heap) (st: pstate) (x: obj_addr)
  : Lemma (requires pages_ok g st /\ all_swept st /\
                    Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))
          (ensures color_at g (hx x) == White)
  = let h = hx x in
    R.obj_iff g x;
    R.hdr_obj g x;
    is_blue_iff x g;
    GC.Spec.Pages.Step.pages_ok_elim g st;
    SA.in_unit g st.pm st.pm h;
    eliminate exists (i: nat{i < n_pages}).
      walk_page st.pm i /\ page_base i <= h /\ h < page_base (i + span st.pm i) /\
      steps_to g (page_base i) h
    with begin
      assert (page_shape g st.pm i);
      match (entry st.pm i).kind with
      | Free -> free_page_only g i h
      | Pool c ->
        slot0 i c;
        SU.pool_pos_from g i c 0 h;
        assert (pool_white g st.pm i)
      | LargeHead n ->
        assert (run_swept_ok g st.pm i);
        assert (run_block g i n h)
    end

/// ---------------------------------------------------------------------------
/// Recolouring a live object
/// ---------------------------------------------------------------------------

/// Whitening `x` after recolouring it is whitening it.
#push-options "--fuel 1"
let whiten_recoloured (g: heap) (x: obj_addr) (ys: list obj_addr) (c: color)
  : Lemma (requires c <> Blue)
          (ensures whiten (set_object_color x g c) (x :: ys) == whiten g (x :: ys))
  = let g1 = set_object_color x g c in
    let zs = x :: ys in
    hd_address_spec x;
    hx_word x;
    sc_eq g x c;
    let aux (b: nat) : Lemma (b < heap_size /\ b % 8 == 0 ==>
                              read_word (whiten g1 zs) (U64.uint_to_t b) == read_word (whiten g zs) (U64.uint_to_t b))
      = if b < heap_size && b % 8 = 0 then begin
          let ba : hp_addr = U64.uint_to_t b in
          paint_read g1 zs White ba;
          paint_read g zs White ba;
          if b = hx x then begin
            assert (ba == hd_address x);
            assert (~(avoid zs b));
            read_write_same g (hd_address x) (colorHeader (read_word g (hd_address x)) c);
            colorHeader_twice (read_word g (hd_address x)) c White
          end
          else begin
            read_write_different g (hd_address x) ba (colorHeader (read_word g (hd_address x)) c);
            assert (read_word g1 ba == read_word g ba)
          end
        end
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext (whiten g1 zs) (whiten g zs)
#pop-options

#push-options "--fuel 2"
let whiten_cons (g: heap) (x: obj_addr) (ys: list obj_addr)
  : Lemma (whiten g (x :: ys) == wr (whiten g ys) (hx x) (colorHeader (hdr (whiten g ys) (hx x)) White))
  = ()
#pop-options

/// Whitening a white object changes nothing.
let whiten_white (g: heap) (x: obj_addr) (ys: list obj_addr)
  : Lemma (requires color_at (whiten g ys) (hx x) == White)
          (ensures whiten g (x :: ys) == whiten g ys)
  = let gw = whiten g ys in
    whiten_cons g x ys;
    hx_word x;
    colorHeader_same (hdr gw (hx x)) White;
    let aux (b: nat) : Lemma (b < heap_size /\ b % 8 == 0 ==>
                              read_word (wr gw (hx x) (hdr gw (hx x))) (U64.uint_to_t b) == read_word gw (U64.uint_to_t b))
      = if b < heap_size && b % 8 = 0 then wr_read gw (hx x) (hdr gw (hx x)) (U64.uint_to_t b)
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext (wr gw (hx x) (hdr gw (hx x))) gw

#push-options "--fuel 1"
let live_cons (g: heap) (x: obj_addr) (ys: list obj_addr)
  : Lemma (requires live_list g ys /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g))
          (ensures live_list g (x :: ys))
  = ()
#pop-options

/// **The mark keeps the invariant**: recolouring a live object any colour
/// but blue.
let mark_inv_recolour (g: heap) (st: pstate) (x: obj_addr) (c: color)
  : Lemma (requires mark_inv g st /\ Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ c <> Blue)
          (ensures mark_inv (set_object_color x g c) st)
  = eliminate exists (ys: list obj_addr). live_list g ys /\ pages_ok (whiten g ys) st
    with begin
      let g1 = set_object_color x g c in
      step_facts g x c;
      set_color_preserves_not_blue x x g c;
      live_cons g1 x ys;
      whiten_facts g ys;
      whiten_objects g ys;
      live_white (whiten g ys) st x;
      whiten_white g x ys;
      whiten_recoloured g x ys c
    end

/// ---------------------------------------------------------------------------
/// Allocation keeps every page swept
/// ---------------------------------------------------------------------------

let upd_swept (pm: page_map) (p: nat{p < n_pages}) (e: page_info)
  : Lemma (requires (forall (i: nat{i < n_pages}). (entry pm i).swept == true) /\ e.swept == true)
          (ensures forall (i: nat{i < n_pages}). (entry (Seq.upd pm p e) i).swept == true)
  = ()

let pop_swept (g: heap) (st: pstate) (c: nat{c < n_cls}) (wz: nat{Pool.small_wz wz c})
  : Lemma (requires all_swept st)
          (ensures (let (_, st', _) = Pool.pop_as false g st c wz in all_swept st'))
  = match pop_at st c with
    | None -> ()
    | Some (p, k) ->
      let e = entry st.pm p in
      upd_swept st.pm p { e with free_head = hdr g (slot_obj p c k); nfree = e.nfree - 1 }

let small_swept (g: heap) (st: pstate) (wz: nat{wz + 1 <= small_max})
  : Lemma (requires all_swept st)
          (ensures (let (_, st', _) = Pool.small_alloc_as false g st wz in all_swept st'))
  = let c = class_of (wz + 1) in
    class_of_fits (wz + 1);
    Pool.small_wz_intro wz c;
    if Pool.avail_at st c <> 0UL then pop_swept g st c wz
    else begin
      let i = Pool.find_free st.pm 0 in
      if i >= n_pages then ()
      else begin
        let st1 = Pool.acq_state st i c in
        upd_swept st.pm i (Pool.acq_entry st i c);
        pop_swept (PI.pool_init g i c) st1 c wz
      end
    end

let run_map_swept (pm: page_map) (i: nat) (k: pos)
  : Lemma (requires forall (j: nat{j < n_pages}). (entry pm j).swept == true)
          (ensures forall (j: nat{j < n_pages}). (entry (NR.run_map pm i k) j).swept == true)
  = ()

let large_swept (g: heap) (st: pstate) (wz: nat{wz < pow2 54})
  : Lemma (requires all_swept st)
          (ensures (let (_, st', _) = A.large_alloc_as false g st wz in all_swept st'))
  = let cs = GC.Spec.Pages.Cells.walk g (GC.Spec.Pages.Cells.large_head st) heap_words in
    match LG.split_fit g cs (wz + 1) with
    | Some (pre, c, post) -> ()
    | None ->
      let k = pages_for (wz + 1) in
      let i = NR.find_run st.pm k 0 in
      if i + k > n_pages then () else run_map_swept st.pm i k

let alloc_swept (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires all_swept st)
          (ensures (let (_, st', _) = A.alloc g st wz in all_swept st'))
  = if wz + 1 >= pow2 54 then ()
    else if wz + 1 <= small_max then small_swept g st wz
    else large_swept g st wz

/// **A black allocation keeps the invariant**: every heap the caller makes
/// by writing the fields satisfies it.
let mark_inv_alloc (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires mark_inv g st)
          (ensures (let (g', st', o) = alloc_col Black g st wz in
                    alloc_ok_col Black g g' st st' wz o /\ all_swept st' /\
                    (o =!= 0UL ==>
                       (forall (g'': heap). fields_written g' g'' (o <: obj_addr) ==> mark_inv g'' st'))))
  = alloc_col_correct Black g st wz;
    alloc_swept g st wz
