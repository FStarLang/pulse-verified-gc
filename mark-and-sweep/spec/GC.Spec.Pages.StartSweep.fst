/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.StartSweep - the step before the sweep
/// ---------------------------------------------------------------------------
///
/// When the mark has finished, the collector empties the lists and marks
/// every page unswept (plan §1.4), as #46's `clear_heads` empties its lists:
/// `start_sweep st` keeps every page's kind, marks every page that is not
/// free unswept, and empties the lists of pages and the large lists.  The
/// heap is not touched.
///
/// **`start_ready`**: from the allocator's invariant while marking
/// (`GC.Spec.Pages.MarkPhase.mark_inv`) and no grey object, it gives the
/// state the sweep starts from (`GC.Spec.Pages.SweepAll.sweep_ready`).
///   - The pages keep their shapes: the walk and which blocks are free do
///     not depend on the colours of live objects (`shape_back`).
///   - No block of a pool page or run is grey: a live object is not grey,
///     and any other block has the colour it has in the whitened heap, where
///     every swept page holds only white and free blocks (L5, L7).
///
/// **`collection_cycle`**: the cycle of the sequential collector, from the
/// marked heap back to the allocator's invariant in `Idle`.

module GC.Spec.Pages.StartSweep

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
open GC.Spec.Pages.Recolour
open GC.Spec.Pages.ColourFacts

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module R = GC.Spec.Pages.Replace
module FLs = GC.Spec.FreeLists
module Mark = GC.Spec.Mark
module SA = GC.Spec.Pages.SweepAll
module AP = GC.Spec.Pages.AllocPhase
module MP = GC.Spec.Pages.MarkPhase
module SW = GC.Spec.Pages.SweepWf

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The step
/// ---------------------------------------------------------------------------

let unsweep (e: page_info) : page_info =
  if e.kind = Free then e else { e with swept = false }

let clear_map (pm: page_map) : page_map =
  Seq.init n_pages (fun (j: nat{j < n_pages}) -> unsweep (entry pm j))

let start_sweep (st: pstate) : pstate = {
  pm = clear_map st.pm;
  avail = Seq.create n_cls 0UL;
  large = FLs.fls_empty;
}

let clear_entry (pm: page_map) (j: nat{j < n_pages})
  : Lemma (entry (clear_map pm) j == unsweep (entry pm j))
  = ()

let clear_map_ok (pm: page_map)
  : Lemma (requires map_ok pm) (ensures map_ok (clear_map pm))
  = FStar.Classical.forall_intro (clear_entry pm);
    let one (i: nat{i < n_pages})
      : Lemma (run_ok (clear_map pm) i /\ cont_ok (clear_map pm) i /\ free_ok (clear_map pm) i)
      = assert (run_ok pm i /\ cont_ok pm i /\ free_ok pm i);
        if (entry pm i).kind = LargeCont then
          eliminate exists (h: nat{h < n_pages}). h < i /\ in_run pm h i
          with assert (in_run (clear_map pm) h i)
    in
    FStar.Classical.forall_intro one

/// ---------------------------------------------------------------------------
/// Shapes do not read the colours of live objects
/// ---------------------------------------------------------------------------

/// Two heaps whose headers agree in size and in which blocks are free.
let same_shape (g1 g2: heap) : prop =
  forall (a: nat). words_at g1 a == words_at g2 a /\ (color_at g1 a == Blue <==> color_at g2 a == Blue)

let whiten_same_shape (g: heap) (ys: list obj_addr)
  : Lemma (requires live_list g ys) (ensures same_shape (whiten g ys) g)
  = let one (a: nat)
      : Lemma (words_at (whiten g ys) a == words_at g a /\
               (color_at (whiten g ys) a == Blue <==> color_at g a == Blue))
      = if a < heap_size && a % 8 = 0 then begin
          let ha = mk_hp_addr a in
          paint_read g ys White ha;
          colorHeader_preserves_wosize (read_word g ha) White;
          colorHeader_getColor (read_word g ha) White;
          if not (FStar.IndefiniteDescription.strong_excluded_middle (avoid ys a)) then
            eliminate exists (y: obj_addr). L.mem y ys /\ hx y == a
            with begin
              R.hdr_obj g y;
              is_blue_iff y g
            end
        end
    in
    FStar.Classical.forall_intro one

#push-options "--fuel 1 --ifuel 1"
let rec steps_same (g1 g2: heap) (a b: nat)
  : Lemma (requires same_shape g1 g2)
          (ensures steps_to g1 a b == steps_to g2 a b)
          (decreases (if a <= b then b - a else 0))
  = if a = b || a > b || b > heap_size || a % 8 <> 0 then ()
    else begin
      let ha = mk_hp_addr a in
      assert (words_at g1 a == words_at g2 a);
      assert (hdr g1 a == read_word g1 ha /\ hdr g2 a == read_word g2 ha);
      let nx = a + block_bytes g1 ha in
      assert (block_bytes g2 ha == block_bytes g1 ha);
      if nx <= b then steps_same g1 g2 nx b
    end
#pop-options

let shape_back (g1 g2: heap) (pm1 pm2: page_map)
  : Lemma (requires shape_ok g1 pm1 /\ same_shape g1 g2 /\ map_ok pm2 /\
                    (forall (i: nat{i < n_pages}). (entry pm2 i).kind == (entry pm1 i).kind))
          (ensures shape_ok g2 pm2)
  = let page (i: nat{i < n_pages}) : Lemma (page_shape g2 pm2 i)
      = assert (page_shape g1 pm1 i);
        match (entry pm1 i).kind with
        | LargeHead n -> steps_same g1 g2 (page_base i) (page_base (i + n))
        | _ -> ()
    in
    FStar.Classical.forall_intro page

/// ---------------------------------------------------------------------------
/// No grey block
/// ---------------------------------------------------------------------------

/// A block that is not grey in the whitened heap is not grey, unless it is
/// one of the live objects, which the mark left not grey either.
let not_grey (g: heap) (ys: list obj_addr) (a: nat)
  : Lemma (requires live_list g ys /\ Mark.noGreyObjects g /\
                    color_at (whiten g ys) a =!= Gray)
          (ensures color_at g a =!= Gray)
  = if a < heap_size && a % 8 = 0 then begin
      let ha = mk_hp_addr a in
      paint_read g ys White ha;
      if not (FStar.IndefiniteDescription.strong_excluded_middle (avoid ys a)) then
        eliminate exists (y: obj_addr). L.mem y ys /\ hx y == a
        with begin
          R.hdr_obj g y;
          is_gray_iff y g
        end
    end

/// ---------------------------------------------------------------------------
/// The theorem
/// ---------------------------------------------------------------------------

let start_ready_ys (g: heap) (st: pstate) (ys: list obj_addr)
  : Lemma (requires live_list g ys /\ pages_ok (whiten g ys) st /\ MP.all_swept st /\
                    Mark.noGreyObjects g)
          (ensures SA.sweep_ready g (start_sweep st))
  = let gw = whiten g ys in
    let st' = start_sweep st in
    GC.Spec.Pages.Step.pages_ok_elim gw st;
    whiten_same_shape g ys;
    FStar.Classical.forall_intro (clear_entry st.pm);
    clear_map_ok st.pm;
    shape_back gw g st.pm st'.pm;
    let pool (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat)
      : Lemma ((entry st'.pm i).kind == Pool c /\ k < n_slots c /\ slot_used g i c k ==>
               color_at g (slot_base i c k) =!= Gray)
      = if (entry st'.pm i).kind = Pool c && k < n_slots c then begin
          assert (pool_white gw st.pm i);
          not_grey g ys (slot_base i c k)
        end
    in
    FStar.Classical.forall_intro_3 pool;
    let run (h: nat{h < n_pages}) (a: nat)
      : Lemma (LargeHead? (entry st'.pm h).kind /\ run_block g h (run_len (entry st'.pm h).kind) a ==>
               color_at g a =!= Gray)
      = if LargeHead? (entry st'.pm h).kind then begin
          let n = run_len (entry st'.pm h).kind in
          steps_same gw g (page_base h) a;
          assert (run_swept_ok gw st.pm h);
          if FStar.IndefiniteDescription.strong_excluded_middle (run_block g h n a) then
            not_grey g ys a
        end
    in
    FStar.Classical.forall_intro_2 run

/// **The step before the sweep.**  From the allocator's invariant while
/// marking and a mark that left no grey object, emptying the lists and
/// marking the pages unswept gives the state the sweep starts from.
let start_ready (g: heap) (st: pstate)
  : Lemma (requires MP.mark_inv g st /\ Mark.noGreyObjects g)
          (ensures SA.sweep_ready g (start_sweep st))
  = eliminate exists (ys: list obj_addr). live_list g ys /\ pages_ok (whiten g ys) st
    with start_ready_ys g st ys

/// **The cycle of the sequential collector.**  A heap in the marking
/// invariant that the mark has finished with (`mark_done`) is swept into
/// the invariant of `Idle`: `pages_ok`, `well_formed_heap`, every page swept.
let collection_cycle (g: heap) (st: pstate)
  : Lemma (requires MP.mark_inv g st /\ SA.mark_done g)
          (ensures (let (g', st') = SA.sweep_all g (start_sweep st) in
                    pages_ok g' st' /\ well_formed_heap g' /\ MP.all_swept st'))
  = start_ready g st;
    SW.sweep_all_wf g (start_sweep st)

/// ---------------------------------------------------------------------------
/// Vacuity
/// ---------------------------------------------------------------------------

/// The empty heap of pages meets the cycle's hypotheses.
let init_cycle (g: heap)
  : Lemma (MP.mark_inv (GC.Spec.Pages.Init.init_heap g) GC.Spec.Pages.Init.init_state /\
           SA.mark_done (GC.Spec.Pages.Init.init_heap g))
  = GC.Spec.Pages.Alloc.init_alloc_pre g;
    MP.mark_inv_of_ok (GC.Spec.Pages.Init.init_heap g) GC.Spec.Pages.Init.init_state;
    GC.Spec.Pages.SweepVacuity.sweep_all_ready g

/// The hypotheses of `start_ready` and `collection_cycle` are not
/// refutable, nor those of `SweepWf.sweep_all_wf`.
#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"
[@@expect_failure [19]]
let start_hyps_not_false (g: heap) (st: pstate)
  : Lemma (requires MP.mark_inv g st /\ Mark.noGreyObjects g) (ensures False)
  = ()

[@@expect_failure [19]]
let cycle_hyps_not_false (g: heap) (st: pstate)
  : Lemma (requires MP.mark_inv g st /\ SA.mark_done g) (ensures False)
  = ()

[@@expect_failure [19]]
let sweep_wf_hyps_not_false (g: heap) (st: pstate)
  : Lemma (requires SA.sweep_ready g st /\ SA.mark_done g) (ensures False)
  = ()
#pop-options
