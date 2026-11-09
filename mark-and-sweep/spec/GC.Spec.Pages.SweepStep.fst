/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.SweepStep - one step of the whole sweep
/// ---------------------------------------------------------------------------
///
/// `GC.Spec.Pages.SweepAll` sweeps the heap unit by unit.  A step sweeps one
/// unit and updates the allocator state around it:
///   - a pool page (`pool_step`): the page sweep, then, if the page kept a
///     free slot, the page goes on its class's list (`push_avail`, the push
///     lemma `push_ok` of plan §2.1);
///   - a run (`run_step`): the run sweep, linking the blocks it lists in
///     front of list 0.
/// Each step keeps the page-local clauses of every page, the class lists
/// (L8) and the large lists (L9, in the list view `lview`), and leaves every
/// other unit alone.
///
/// The large lists hold cells of swept runs only, so a step that leaves the
/// swept runs alone keeps them (`lview_frame`); the run step adds its own
/// cells in front (`lview_run`).

module GC.Spec.Pages.SweepStep

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
open GC.Spec.Pages.Cells
open GC.Spec.Pages.Theorems

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module FLs = GC.Spec.FreeLists
module R = GC.Spec.Pages.Replace
module SU = GC.Spec.Pages.SweepUnits
module NR = GC.Spec.Pages.NewRun
module SP = GC.Spec.Pages.SweepPage
module SR = GC.Spec.Pages.SweepRun

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The class lists: pushing a swept pool page
/// ---------------------------------------------------------------------------

let n_pages_small () : Lemma (n_pages < pow2 57)
  = assert (n_pages <= heap_size - U64.v zero_addr)

/// The list entry of page `i`: its index plus one.
let page_id (i: nat{i < n_pages}) : U64.t =
  n_pages_small ();
  FStar.Math.Lemmas.pow2_lt_compat 64 57;
  U64.uint_to_t (i + 1)

/// Page `i` is swept into entry `e`; if it is a pool page with a free slot,
/// it goes in front of its class's list.
let push_avail (st: pstate) (i: nat{i < n_pages}) (e: page_info) : pstate =
  match e.kind with
  | Pool c ->
    if e.nfree > 0 && Seq.length st.avail = n_cls then
      { st with pm = Seq.upd st.pm i ({ e with next = Seq.index st.avail c });
                avail = Seq.upd st.avail c (page_id i) }
    else { st with pm = Seq.upd st.pm i e }
  | _ -> { st with pm = Seq.upd st.pm i e }

let push_entry (st: pstate) (i: nat{i < n_pages}) (e: page_info)
  : Lemma (let st' = push_avail st i e in
           st'.large == st.large /\
           (entry st'.pm i).kind == e.kind /\ (entry st'.pm i).swept == e.swept /\
           (entry st'.pm i).free_head == e.free_head /\ (entry st'.pm i).nfree == e.nfree /\
           (forall (j: nat{j < n_pages}). j <> i ==> entry st'.pm j == entry st.pm j))
  = ()

#push-options "--fuel 1"
/// **The push lemma.**  Page `i`, with no free slot listed before, swept
/// into entry `e`: the class lists stay exact.
let push_ok (st: pstate) (i: nat{i < n_pages}) (e: page_info)
  : Lemma (requires avail_ok st /\ (forall (c: nat{c < n_cls}). not (has_free_slot st.pm c i)) /\
                    e.swept == true)
          (ensures avail_ok (push_avail st i e))
  = let st' = push_avail st i e in
    push_entry st i e;
    let per (d: nat{d < n_cls})
      : Lemma (exists (ps: list nat).
                 page_chain st'.pm (Seq.index st'.avail d) ps /\ L.noRepeats ps /\
                 (forall (p: nat{p < n_pages}). L.mem p ps <==> has_free_slot st'.pm d p))
      = eliminate exists (ps: list nat).
          page_chain st.pm (Seq.index st.avail d) ps /\ L.noRepeats ps /\
          (forall (p: nat{p < n_pages}). L.mem p ps <==> has_free_slot st.pm d p)
        with begin
          assert (~(L.mem i ps));
          page_chain_frame st.pm st'.pm (Seq.index st.avail d) ps;
          match e.kind with
          | Pool c ->
            if e.nfree > 0 && c = d then begin
              assert (Seq.index st'.avail d == page_id i);
              assert (page_chain st'.pm (Seq.index st'.avail d) (i :: ps))
            end
          | _ -> ()
        end
    in
    FStar.Classical.forall_intro per
#pop-options

/// A pool page swept into a pool page or a free page keeps the map well
/// formed.
let map_ok_pool (pm: page_map) (i: nat{i < n_pages}) (e: page_info)
  : Lemma (requires map_ok pm /\ Pool? (entry pm i).kind /\ (Pool? e.kind \/ e.kind == Free) /\
                    e.swept == true)
          (ensures map_ok (Seq.upd pm i e))
  = let pm' = Seq.upd pm i e in
    let aux (j: nat{j < n_pages}) : Lemma (run_ok pm' j /\ cont_ok pm' j /\ free_ok pm' j)
      = assert (run_ok pm j /\ cont_ok pm j /\ free_ok pm j);
        if j <> i then begin
          match (entry pm j).kind with
          | LargeCont ->
            eliminate exists (u: nat{u < n_pages}). u < j /\ in_run pm u j
            with assert (in_run pm' u j)
          | _ -> ()
        end
    in
    FStar.Classical.forall_intro aux

/// ---------------------------------------------------------------------------
/// Objects of a run that is left alone
/// ---------------------------------------------------------------------------

/// A block of a run, as an object: its header is a step of the walk over the
/// run, and its block lies in the run.
let run_obj (g: heap) (pm: page_map) (u: nat{u < n_pages}) (y: obj_addr)
  : Lemma (requires shape_ok g pm /\ LargeHead? (entry pm u).kind /\ Seq.mem y (objects zero_addr g) /\
                    page_base u <= U64.v y - 8 /\ U64.v y - 8 < page_base (u + run_len (entry pm u).kind))
          (ensures run_block g u (run_len (entry pm u).kind) (U64.v y - 8) /\
                   U64.v y - 8 + words_at g (U64.v y - 8) * 8 <= page_base (u + run_len (entry pm u).kind))
  = let n = run_len (entry pm u).kind in
    walk_pages_reached g pm u;
    objects_steps_to g zero_addr y;
    hd_address_spec y;
    R.steps_to_det g (U64.v zero_addr) (page_base u) (U64.v y - 8);
    assert (page_shape g pm u);
    R.block_before g (page_base u) (U64.v y - 8) (page_base (u + n))

/// The converse: a block of a run is an object.
let obj_of_run (g: heap) (pm: page_map) (u: nat{u < n_pages}) (y: obj_addr)
  : Lemma (requires shape_ok g pm /\ LargeHead? (entry pm u).kind /\
                    run_block g u (run_len (entry pm u).kind) (U64.v y - 8))
          (ensures Seq.mem y (objects zero_addr g))
  = let n = run_len (entry pm u).kind in
    walk_pages_reached g pm u;
    assert (page_shape g pm u);
    R.block_before g (page_base u) (U64.v y - 8) (page_base (u + n));
    steps_to_trans g (U64.v zero_addr) (page_base u) (U64.v y - 8);
    page_base_mono (u + n) n_pages;
    pages_end_bound ();
    R.obj_iff g y

/// **An object of a run whose words are kept is an object of the new heap**,
/// with the same header and first field.
let run_transfer (g g': heap) (pm pm': page_map) (u: nat{u < n_pages}) (y: obj_addr)
  : Lemma (requires shape_ok g pm /\ shape_ok g' pm' /\
                    LargeHead? (entry pm u).kind /\ entry pm' u == entry pm u /\
                    kept_range g g' (page_base u) (page_base (u + run_len (entry pm u).kind)) /\
                    Seq.mem y (objects zero_addr g) /\
                    page_base u <= U64.v y - 8 /\ U64.v y - 8 < page_base (u + run_len (entry pm u).kind))
          (ensures Seq.mem y (objects zero_addr g') /\
                   read_word g' (hd_address y) == read_word g (hd_address y) /\
                   (U64.v (wosize_of_object y g) >= 1 ==>
                      read_word g' (y <: hp_addr) == read_word g (y <: hp_addr)))
  = let n = run_len (entry pm u).kind in
    run_obj g pm u y;
    run_block_frame g g' u n (U64.v y - 8);
    obj_of_run g' pm' u y;
    hd_address_spec y;
    R.hdr_obj g y

/// ---------------------------------------------------------------------------
/// The large lists, when the swept runs are left alone
/// ---------------------------------------------------------------------------

/// The swept runs of `pm` are runs of `pm'`, with their words kept.
let runs_fwd (g g': heap) (pm pm': page_map) : prop =
  forall (h: nat{h < n_pages}). LargeHead? (entry pm h).kind /\ (entry pm h).swept ==>
    entry pm' h == entry pm h /\
    kept_range g g' (page_base h) (page_base (span_end pm h))

let runs_kept (g g': heap) (pm pm': page_map) : prop =
  runs_fwd g g' pm pm' /\ runs_fwd g' g pm' pm

/// A listable block of `g` is a listable block of `g'`, the same block.
let listable_transfer (g g': heap) (pm pm': page_map) (y: obj_addr)
  : Lemma (requires shape_ok g pm /\ shape_ok g' pm' /\ runs_fwd g g' pm pm' /\
                    Seq.mem y (objects zero_addr g) /\ large_listable g pm y)
          (ensures Seq.mem y (objects zero_addr g') /\
                   read_word g' (hd_address y) == read_word g (hd_address y) /\
                   (U64.v (wosize_of_object y g) >= 1 ==>
                      read_word g' (y <: hp_addr) == read_word g (y <: hp_addr)) /\
                   is_blue y g' == is_blue y g /\
                   wosize_of_object y g' == wosize_of_object y g /\
                   large_listable g' pm' y)
  = eliminate exists (u: nat{u < n_pages}).
      LargeHead? (entry pm u).kind /\ (entry pm u).swept /\
      page_base u <= U64.v (hd_address y) /\ U64.v (hd_address y) < page_base (u + run_len (entry pm u).kind)
    with begin
      hd_address_spec y;
      run_transfer g g' pm pm' u y;
      color_of_header_eq y g g';
      wosize_of_object_spec y g;
      wosize_of_object_spec y g';
      assert (in_swept_run pm' (U64.v (hd_address y)))
    end

/// **The large lists are kept when the swept runs are.**
let lview_frame (g g': heap) (st st': pstate) (cs: list obj_addr)
  : Lemma (requires lview g st cs /\ shape_ok g st.pm /\ shape_ok g' st'.pm /\
                    st'.large == st.large /\ runs_kept g g' st.pm st'.pm)
          (ensures lview g' st' cs)
  = let in_cs (y: obj_addr)
      : Lemma (requires L.mem y cs)
              (ensures Seq.mem y (objects zero_addr g') /\ U64.v (wosize_of_object y g') >= 1 /\
                       read_word g' (y <: hp_addr) == read_word g (y <: hp_addr) /\
                       is_blue y g' /\ large_listable g' st'.pm y)
      = cells_mem g (large_head st) cs y;
        listable_transfer g g' st.pm st'.pm y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires in_cs);
    cells_frame g g' (large_head st) cs;
    let complete (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g') /\ is_blue y g' /\ large_listable g' st'.pm y)
              (ensures L.mem y cs)
      = listable_transfer g' g st'.pm st.pm y
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires complete)

/// ---------------------------------------------------------------------------
/// The large lists after a run is swept
/// ---------------------------------------------------------------------------

/// A stretch of links, then a list of cells, is a list of cells.
#push-options "--fuel 1"
let rec cells_prepend (g: heap) (fp: U64.t) (xs: list obj_addr) (tl: U64.t) (cs: list obj_addr)
  : Lemma (requires lchain g fp xs tl /\ cells g tl cs /\ L.noRepeats (L.append xs cs) /\
                    L.length cs <= heap_words /\
                    (forall (x: obj_addr). L.mem x xs ==>
                       Seq.mem x (objects zero_addr g) /\ U64.v (wosize_of_object x g) >= 1))
          (ensures cells g fp (L.append xs cs) /\ L.length (L.append xs cs) <= heap_words)
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: xs' ->
      let nx = read_word g (x <: hp_addr) in
      cells_prepend g nx xs' tl cs;
      NR.push_len g nx (L.append xs' cs) x;
      NR.push_cells g x (L.append xs' cs) nx
#pop-options

/// A swept run other than the run at `p` lies apart from it.
let apart_run (pm: page_map) (p: nat{p < n_pages}) (u: nat{u < n_pages}) (a: nat)
  : Lemma (requires map_ok pm /\ LargeHead? (entry pm p).kind /\ LargeHead? (entry pm u).kind /\ u <> p /\
                    page_base u <= a /\ a < page_base (u + run_len (entry pm u).kind))
          (ensures a < page_base p \/ a >= page_base (p + run_len (entry pm p).kind))
  = let n = run_len (entry pm p).kind in
    let m = run_len (entry pm u).kind in
    GC.Spec.Pages.RunMap.other_run pm p n u;
    if u + m <= p then page_base_mono (u + m) p
    else page_base_mono (p + n) u

/// The setting of the run step.
let run_step_ctx (g g': heap) (st: pstate) (p: nat{p < n_pages}) (pm': page_map) (fp': U64.t) : prop =
  shape_ok g st.pm /\ shape_ok g' pm' /\ marked_run g st.pm p /\
  sweep_run_ok g st.pm p (large_head st) g' pm' fp'

/// The frame of the run step, alone.
let run_frame_facts (g g': heap) (pm pm': page_map) (p: nat{p < n_pages}) : prop =
  map_ok pm /\ LargeHead? (entry pm p).kind /\ not (entry pm p).swept /\
  (forall (a: hp_addr). U64.v a < page_base p \/ U64.v a >= page_base (p + run_len (entry pm p).kind) ==>
     read_word g' a == read_word g a) /\
  (forall (j: nat{j < n_pages}). j < p \/ j >= p + run_len (entry pm p).kind ==> entry pm' j == entry pm j)

let run_frame_of (g g': heap) (st: pstate) (p: nat{p < n_pages}) (pm': page_map) (fp': U64.t)
  : Lemma (requires run_step_ctx g g' st p pm' fp') (ensures run_frame_facts g g' st.pm pm' p)
  = ()

/// One old swept run.
let old_run (g g': heap) (pm pm': page_map) (p: nat{p < n_pages}) (u: nat{u < n_pages})
  : Lemma (requires run_frame_facts g g' pm pm' p /\ LargeHead? (entry pm u).kind /\ (entry pm u).swept)
          (ensures entry pm' u == entry pm u /\
                   kept_range g g' (page_base u) (page_base (span_end pm u)))
  = let n = run_len (entry pm p).kind in
    GC.Spec.Pages.RunMap.other_run pm p n u;
    let m = run_len (entry pm u).kind in
    if u + m <= p then page_base_mono (u + m) p
    else page_base_mono (p + n) u

/// An old swept run is a run of the new map, its words kept.
let old_runs (g g': heap) (st: pstate) (p: nat{p < n_pages}) (pm': page_map) (fp': U64.t)
  : Lemma (requires run_step_ctx g g' st p pm' fp')
          (ensures runs_fwd g g' st.pm pm')
  = run_frame_of g g' st p pm' fp';
    FStar.Classical.forall_intro (FStar.Classical.move_requires (old_run g g' st.pm pm' p))

/// A swept run of the new map outside the swept run's pages is an old one.
let new_runs_out (g g': heap) (st: pstate) (p: nat{p < n_pages}) (pm': page_map) (fp': U64.t) (u: nat{u < n_pages}) (a: nat)
  : Lemma (requires run_step_ctx g g' st p pm' fp' /\
                    LargeHead? (entry pm' u).kind /\ (entry pm' u).swept /\
                    page_base u <= a /\ a < page_base (u + run_len (entry pm' u).kind) /\
                    (a < page_base p \/ a >= page_base (p + run_len (entry st.pm p).kind)))
          (ensures (u < p \/ u >= p + run_len (entry st.pm p).kind) /\
                   entry st.pm u == entry pm' u /\
                   kept_range g' g (page_base u) (page_base (u + run_len (entry pm' u).kind)))
  = let n = run_len (entry st.pm p).kind in
    let m = run_len (entry pm' u).kind in
    if p <= u && u < p + n then begin
      assert (u + m <= p + n);
      page_base_mono p u;
      page_base_mono (u + m) (p + n)
    end else begin
      assert (run_ok st.pm u);
      assert (run_ok st.pm p);
      GC.Spec.Pages.RunMap.other_run st.pm p n u;
      if u + m <= p then page_base_mono (u + m) p
      else page_base_mono (p + n) u
    end

let lg_min_pos () : Lemma (lg_min >= 2) = cls_bounds (n_cls - 1)

/// The state after the run step.
let run_state (st: pstate) (pm': page_map) (fp': U64.t) : pstate =
  { st with pm = pm'; large = FLs.fls_set st.large 0 fp' }

/// A block the run sweep lists is a listable free block of the new heap.
let new_cell_core (g': heap) (pm': page_map) (p: nat{p < n_pages}) (e: nat) (y: obj_addr)
  : Lemma (requires shape_ok g' pm' /\ (entry pm' p).kind =!= LargeCont /\
                    steps_to g' (page_base p) e /\ e <= pages_end /\
                    (let s = page_base p in
                     s <= U64.v y - 8 /\ U64.v y - 8 < e /\ steps_to g' s (U64.v y - 8) /\
                     color_at g' (U64.v y - 8) == Blue /\ words_at g' (U64.v y - 8) >= lg_min /\
                     in_swept_run pm' (U64.v y - 8)))
          (ensures Seq.mem y (objects zero_addr g') /\ U64.v (wosize_of_object y g') >= 1 /\
                   is_blue y g' /\ large_listable g' pm' y)
  = let s = page_base p in
    let h = U64.v y - 8 in
    walk_pages_reached g' pm' p;
    steps_to_trans g' (U64.v zero_addr) s h;
    R.block_before g' s h e;
    pages_end_bound ();
    lg_min_pos ();
    hd_address_spec y;
    R.obj_iff g' y;
    R.hdr_obj g' y;
    is_blue_iff y g'

let new_cell (g g': heap) (st: pstate) (p: nat{p < n_pages}) (pm': page_map) (fp': U64.t) (y: obj_addr)
  : Lemma (requires run_step_ctx g g' st p pm' fp' /\
                    (let s = page_base p in
                     let e = page_base (p + run_len (entry st.pm p).kind) in
                     s <= U64.v y - 8 /\ U64.v y - 8 < e /\ steps_to g' s (U64.v y - 8) /\
                     color_at g' (U64.v y - 8) == Blue /\ words_at g' (U64.v y - 8) >= lg_min /\
                     in_swept_run pm' (U64.v y - 8)))
          (ensures Seq.mem y (objects zero_addr g') /\ U64.v (wosize_of_object y g') >= 1 /\
                   is_blue y g' /\ large_listable g' pm' y)
  = let n = run_len (entry st.pm p).kind in
    assert (run_ok st.pm p);
    page_base_mono (p + n) n_pages;
    assert ((entry pm' p).kind =!= LargeCont);
    new_cell_core g' pm' p (page_base (p + n)) y

/// A listable free block of the new heap in the swept run is listed by the
/// run sweep.
let new_listable (g g': heap) (st: pstate) (p: nat{p < n_pages}) (pm': page_map) (fp': U64.t) (y: obj_addr)
  : Lemma (requires run_step_ctx g g' st p pm' fp' /\
                    Seq.mem y (objects zero_addr g') /\ is_blue y g' /\ large_listable g' pm' y /\
                    page_base p <= U64.v y - 8 /\ U64.v y - 8 < page_base (p + run_len (entry st.pm p).kind))
          (ensures (let s = page_base p in
                    let h = U64.v y - 8 in
                    steps_to g' s h /\ color_at g' h == Blue /\ words_at g' h >= lg_min /\
                    in_swept_run pm' h))
  = let s = page_base p in
    let h = U64.v y - 8 in
    assert ((entry pm' p).kind =!= LargeCont);
    walk_pages_reached g' pm' p;
    objects_steps_to g' zero_addr y;
    hd_address_spec y;
    R.steps_to_det g' (U64.v zero_addr) s h;
    R.hdr_obj g' y;
    is_blue_iff y g'


/// **The large lists after the run step**: the run's listed blocks, then the
/// old list.
let lview_run (g g': heap) (st: pstate) (p: nat{p < n_pages}) (pm': page_map) (fp': U64.t)
              (cs: list obj_addr)
  : Lemma (requires run_step_ctx g g' st p pm' fp' /\ lview g st cs)
          (ensures exists (cs': list obj_addr). lview g' (run_state st pm' fp') cs')
  = let n = run_len (entry st.pm p).kind in
    let s = page_base p in
    let e = page_base (p + n) in
    let st' = run_state st pm' fp' in
    old_runs g g' st p pm' fp';
    eliminate exists (xs: list obj_addr).
      lchain g' fp' xs (large_head st) /\ L.noRepeats xs /\
      (forall (y: obj_addr).
         L.mem y xs <==>
         (s <= U64.v y - 8 /\ U64.v y - 8 < e /\ steps_to g' s (U64.v y - 8) /\
          color_at g' (U64.v y - 8) == Blue /\ words_at g' (U64.v y - 8) >= lg_min /\
          in_swept_run pm' (U64.v y - 8)))
    with begin
      (* the old cells: in old swept runs, apart from the run *)
      let old_cell (y: obj_addr)
        : Lemma (requires L.mem y cs)
                (ensures Seq.mem y (objects zero_addr g') /\ U64.v (wosize_of_object y g') >= 1 /\
                         read_word g' (y <: hp_addr) == read_word g (y <: hp_addr) /\
                         is_blue y g' /\ large_listable g' st'.pm y /\
                         (U64.v y - 8 < s \/ U64.v y - 8 >= e))
        = cells_mem g (large_head st) cs y;
          listable_transfer g g' st.pm pm' y;
          hd_address_spec y;
          eliminate exists (u: nat{u < n_pages}).
            LargeHead? (entry st.pm u).kind /\ (entry st.pm u).swept /\
            page_base u <= U64.v y - 8 /\ U64.v y - 8 < page_base (u + run_len (entry st.pm u).kind)
          with apart_run st.pm p u (U64.v y - 8)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires old_cell);
      cells_frame g g' (large_head st) cs;
      (* the new cells *)
      FStar.Classical.forall_intro (FStar.Classical.move_requires (new_cell g g' st p pm' fp'));
      (* no cell twice *)
      let apart (y: obj_addr) : Lemma (~(L.mem y xs /\ L.mem y cs))
        = if L.mem y cs then old_cell y
      in
      FStar.Classical.forall_intro apart;
      L.noRepeats_append_intro xs cs;
      cells_prepend g' fp' xs (large_head st) cs;
      NR.push_heads st fp';
      let cs' = L.append xs cs in
      let mem (y: obj_addr) : Lemma (L.mem y cs' <==> L.mem y xs \/ L.mem y cs)
        = L.append_mem xs cs y
      in
      FStar.Classical.forall_intro mem;
      (* every listable free block is listed *)
      let complete (y: obj_addr)
        : Lemma (requires Seq.mem y (objects zero_addr g') /\ is_blue y g' /\ large_listable g' st'.pm y)
                (ensures L.mem y cs')
        = hd_address_spec y;
          if s <= U64.v y - 8 && U64.v y - 8 < e then new_listable g g' st p pm' fp' y
          else
            eliminate exists (u: nat{u < n_pages}).
              LargeHead? (entry pm' u).kind /\ (entry pm' u).swept /\
              page_base u <= U64.v y - 8 /\ U64.v y - 8 < page_base (u + run_len (entry pm' u).kind)
            with begin
              new_runs_out g g' st p pm' fp' u (U64.v y - 8);
              run_transfer g' g pm' st.pm u y;
              color_of_header_eq y g' g;
              wosize_of_object_spec y g;
              wosize_of_object_spec y g';
              assert (in_swept_run st.pm (U64.v (hd_address y)))
            end
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires complete);
      assert (lview g' st' cs')
    end

/// ---------------------------------------------------------------------------
/// The two steps
/// ---------------------------------------------------------------------------

let aligned_lt (x y: nat)
  : Lemma (requires x % 8 == 0 /\ y % 8 == 0 /\ x < y) (ensures x + 8 <= y)
  = FStar.Math.Lemmas.lemma_div_exact x 8;
    FStar.Math.Lemmas.lemma_div_exact y 8

/// The words the page sweep keeps.
let pool_frame (g g': heap) (p: nat{p < n_pages})
  : Lemma (requires page_frame g g' p)
          (ensures forall (x: hp_addr). U64.v x < page_base p \/ U64.v x >= page_base (p + 1) ==>
                     read_word g' x == read_word g x)
  = page_base_aligned p;
    let aux (x: hp_addr)
      : Lemma (U64.v x < page_base p ==> U64.v x + 8 <= page_base p)
      = if U64.v x < page_base p then aligned_lt (U64.v x) (page_base p)
    in
    FStar.Classical.forall_intro aux

/// The pool page's own clauses, under the entry the push leaves.
let pool_own (g': heap) (pm1 pm2: page_map) (p: nat{p < n_pages})
  : Lemma (requires (entry pm2 p).kind == (entry pm1 p).kind /\ (entry pm2 p).swept == (entry pm1 p).swept /\
                    (entry pm2 p).free_head == (entry pm1 p).free_head /\
                    (entry pm2 p).nfree == (entry pm1 p).nfree /\
                    pool_list_ok g' pm1 p /\ pool_white g' pm1 p /\ page_shape g' pm1 p /\
                    ~(LargeHead? (entry pm1 p).kind))
          (ensures page_local g' pm2 p)
  = ()

/// What the page sweep leaves of the page itself.
let pool_own_of (g g': heap) (st: pstate) (p: nat{p < n_pages}) (c: nat{c < n_cls}) (e: page_info)
  : Lemma (requires marked_pool_page g st.pm p c /\ sweep_page_ok g st.pm p c g' e)
          (ensures page_local g' (push_avail st p e).pm p /\ e.swept == true /\
                   (Pool? e.kind \/ e.kind == Free) /\
                   (forall (x: hp_addr). U64.v x < page_base p \/ U64.v x >= page_base (p + 1) ==>
                      read_word g' x == read_word g x))
  = push_entry st p e;
    pool_frame g g' p;
    pool_own g' (Seq.upd st.pm p e) (push_avail st p e).pm p

/// The other pages keep their clauses.
let others_pool (g g': heap) (pm pm': page_map) (p: nat{p < n_pages})
  : Lemma (requires map_ok pm /\ Pool? (entry pm p).kind /\
                    (forall (i: nat{i < n_pages}). page_local g pm i) /\
                    (forall (x: hp_addr). U64.v x < page_base p \/ U64.v x >= page_base (p + 1) ==>
                       read_word g' x == read_word g x) /\
                    (forall (j: nat{j < n_pages}). j <> p ==> entry pm' j == entry pm j))
          (ensures forall (j: nat{j < n_pages}). j <> p ==> page_local g' pm' j)
  = GC.Spec.Pages.Step.others_local g g' pm pm' p (p + 1)

/// The pages after a pool step.
let pool_pages_core (g g': heap) (st: pstate) (p: nat{p < n_pages}) (e: page_info)
  : Lemma (requires map_ok st.pm /\ Pool? (entry st.pm p).kind /\
                    (forall (i: nat{i < n_pages}). page_local g st.pm i) /\ tail_shape g /\
                    (forall (x: hp_addr). U64.v x < page_base p \/ U64.v x >= page_base (p + 1) ==>
                       read_word g' x == read_word g x) /\
                    page_local g' (push_avail st p e).pm p /\ e.swept == true /\
                    (Pool? e.kind \/ e.kind == Free))
          (ensures (let st' = push_avail st p e in
                    shape_ok g' st'.pm /\ (forall (i: nat{i < n_pages}). page_local g' st'.pm i) /\
                    (forall (j: nat{j < n_pages}). j <> p ==> entry st'.pm j == entry st.pm j) /\
                    (entry st'.pm p).swept == true /\ (entry st'.pm p).kind =!= LargeCont))
  = let st' = push_avail st p e in
    push_entry st p e;
    others_pool g g' st.pm st'.pm p;
    GC.Spec.Pages.Step.tail_kept g g' (p + 1);
    map_ok_pool st.pm p (entry st'.pm p);
    assert (Seq.equal st'.pm (Seq.upd st.pm p (entry st'.pm p)))

let pool_pages (g g': heap) (st: pstate) (p: nat{p < n_pages}) (c: nat{c < n_cls}) (e: page_info)
  : Lemma (requires marked_pool_page g st.pm p c /\ shape_ok g st.pm /\
                    (forall (i: nat{i < n_pages}). page_local g st.pm i) /\
                    sweep_page_ok g st.pm p c g' e)
          (ensures (let st' = push_avail st p e in
                    shape_ok g' st'.pm /\ (forall (i: nat{i < n_pages}). page_local g' st'.pm i) /\
                    (forall (x: hp_addr). U64.v x < page_base p \/ U64.v x >= page_base (p + 1) ==>
                       read_word g' x == read_word g x) /\
                    (forall (j: nat{j < n_pages}). j <> p ==> entry st'.pm j == entry st.pm j) /\
                    (entry st'.pm p).swept == true /\ (entry st'.pm p).kind =!= LargeCont))
  = pool_own_of g g' st p c e;
    pool_pages_core g g' st p e

/// The swept runs are left alone by a pool step.
let pool_runs (g g': heap) (st: pstate) (p: nat{p < n_pages}) (e: page_info)
  : Lemma (requires map_ok st.pm /\ Pool? (entry st.pm p).kind /\ ~(LargeHead? e.kind) /\
                    (forall (x: hp_addr). U64.v x < page_base p \/ U64.v x >= page_base (p + 1) ==>
                       read_word g' x == read_word g x))
          (ensures runs_kept g g' st.pm (push_avail st p e).pm)
  = push_entry st p e;
    let runs (u: nat{u < n_pages})
      : Lemma (LargeHead? (entry st.pm u).kind ==>
               kept_range g g' (page_base u) (page_base (span_end st.pm u)))
      = if LargeHead? (entry st.pm u).kind then GC.Spec.Pages.Step.span_apart st.pm p (p + 1) u
    in
    FStar.Classical.forall_intro runs

/// **A pool step.**
let pool_step (g: heap) (st: pstate) (p: nat{p < n_pages}) (c: nat{c < n_cls}) (cs: list obj_addr)
  : Lemma (requires marked_pool_page g st.pm p c /\ shape_ok g st.pm /\
                    (forall (i: nat{i < n_pages}). page_local g st.pm i) /\ avail_ok st /\ lview g st cs)
          (ensures (let (g', e) = SP.sweep_page g st.pm p in
                    let st' = push_avail st p e in
                    shape_ok g' st'.pm /\ (forall (i: nat{i < n_pages}). page_local g' st'.pm i) /\
                    avail_ok st' /\ lview g' st' cs /\
                    (forall (x: hp_addr). U64.v x < page_base p \/ U64.v x >= page_base (p + 1) ==>
                       read_word g' x == read_word g x) /\
                    (forall (j: nat{j < n_pages}). j <> p ==> entry st'.pm j == entry st.pm j) /\
                    (entry st'.pm p).swept == true /\ (entry st'.pm p).kind =!= LargeCont /\
                    SU.unit_ok g g' p 1))
  = SP.sweep_page_correct ();
    let (g', e) = SP.sweep_page g st.pm p in
    assert (sweep_page_ok g st.pm p c g' e);
    let st' = push_avail st p e in
    pool_pages g g' st p c e;
    push_ok st p e;
    pool_runs g g' st p e;
    push_entry st p e;
    lview_frame g g' st st' cs;
    SU.pool_unit_ok g g' st.pm p c e

/// **A run step.**
let run_step (g: heap) (st: pstate) (p: nat{p < n_pages}) (n: pos) (cs: list obj_addr)
  : Lemma (requires marked_run g st.pm p /\ (entry st.pm p).kind == LargeHead n /\ shape_ok g st.pm /\
                    (forall (i: nat{i < n_pages}). page_local g st.pm i) /\ avail_ok st /\ lview g st cs)
          (ensures (let (g', pm', fp') = SR.sweep_run g st.pm p (large_head st) in
                    let st' = run_state st pm' fp' in
                    p + n <= n_pages /\
                    shape_ok g' st'.pm /\ (forall (i: nat{i < n_pages}). page_local g' st'.pm i) /\
                    avail_ok st' /\ (exists (cs': list obj_addr). lview g' st' cs') /\
                    (forall (x: hp_addr). U64.v x < page_base p \/ U64.v x >= page_base (p + n) ==>
                       read_word g' x == read_word g x) /\
                    (forall (j: nat{j < n_pages}). j < p \/ j >= p + n ==> entry st'.pm j == entry st.pm j) /\
                    (forall (j: nat{j < n_pages}). p <= j /\ j < p + n ==> (entry st'.pm j).swept == true) /\
                    (entry st'.pm p).kind =!= LargeCont /\
                    SU.unit_ok g g' p n))
  = SR.sweep_run_correct ();
    let (g', pm', fp') = SR.sweep_run g st.pm p (large_head st) in
    assert (sweep_run_ok g st.pm p (large_head st) g' pm' fp');
    let st' = run_state st pm' fp' in
    assert (run_ok st.pm p);
    (* the pages *)
    GC.Spec.Pages.Step.others_local g g' st.pm pm' p (p + n);
    let inside (j: nat{j < n_pages}) : Lemma (p <= j /\ j < p + n ==> page_local g' pm' j)
      = ()
    in
    FStar.Classical.forall_intro inside;
    GC.Spec.Pages.Step.tail_kept g g' (p + n);
    assert (shape_ok g' pm');
    (* the class lists *)
    let slots (d: nat{d < n_cls}) (q: nat{q < n_pages})
      : Lemma (has_free_slot pm' d q == has_free_slot st.pm d q /\
               (has_free_slot st.pm d q ==> (entry pm' q).next == (entry st.pm q).next))
      = if p <= q && q < p + n then () else ()
    in
    FStar.Classical.forall_intro_2 slots;
    avail_frame st st';
    (* the large lists *)
    lview_run g g' st p pm' fp' cs;
    SU.run_unit_ok g g' st.pm pm' p (large_head st) fp'
