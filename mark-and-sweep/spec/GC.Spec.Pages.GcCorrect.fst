/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.GcCorrect - the sequential collector with the page allocator
/// ---------------------------------------------------------------------------
///
/// `gc_correct_pages`: the heap and allocator state that one collection
/// leaves, from a heap in the allocator's `Idle` invariant, are
///
///   - safe (`gc_safe_pages`): nothing reachable is lost, and the allocator
///     can run again; and
///   - live (`gc_live_pages`): everything unreachable is reclaimed, listed
///     for reuse, and no memory is lost.
///
/// The headings and every clause that does not name the coalescing sweep or
/// its free lists are `GC.Impl.Correct.gc_correct`'s, word for word.  The
/// others are restated for pages (plan §2.3); docs/pages-allocator-proof-plan.md
/// §14 sets the two side by side.
///
/// The collection (`collection`) greys the roots (`GC.Spec.Pages.Darken`),
/// marks (`GC.Spec.Mark.mark`, with the roots as the stack), then runs
/// `start_sweep` and `sweep_all` (`collect`).  `gc_correct_gen` proves the
/// clauses for any mark that leaves `GP.marked` and the allocator's marking
/// invariant; the mark keeps that invariant by `GC.Spec.Pages.MarkSteps`.
///
/// The roots must be greyed first: in `Idle` every live object is white, and
/// the mark needs grey roots (`mark_pre`), so `Idle` and `mark_pre` together
/// allow no root at all (`idle_mark_pre_empty`).
///
/// `reach` is the explicit cycle: any run of allocations, through the
/// allocator interface with the caller's field writes, and collections,
/// from the empty heap of pages.  Every state it reaches is in the `Idle`
/// invariant (`reach_inv`), and every collection in it is correct
/// (`cycle_correct`).

module GC.Spec.Pages.GcCorrect

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Pages.Wf
module Wf = GC.Spec.Pages.Wf
open GC.Lib.Header
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Walk
open GC.Spec.Pages.Shape
open GC.Spec.Pages.Inv

module U64 = FStar.UInt64
module Seq = FStar.Seq
module R = GC.Spec.Pages.Replace
module FLs = GC.Spec.FreeLists
module FL = GC.Spec.FreeList
module SC = GC.Spec.SizeClass
module I = GC.Spec.AllocIface
module PA = GC.Spec.Pages.Allocator
module SA = GC.Spec.Pages.SweepAll
module SS = GC.Spec.Pages.StartSweep
module ST = GC.Spec.Pages.SweepTags
module MP = GC.Spec.Pages.MarkPhase
module MS = GC.Spec.Pages.MarkSteps
module D = GC.Spec.Pages.Darken
module SV = GC.Spec.Pages.Survive
module GP = GC.Spec.Pages.GcPillars
module SPo = GC.Spec.Pages.SweepPools
module Init = GC.Spec.Pages.Init
module PT = GC.Spec.Pages.Partition
module Corr = GC.Spec.Correctness
module Mark = GC.Spec.Mark
module MarkInv = GC.Spec.MarkInv
module HeapModel = GC.Spec.HeapModel

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The collector
/// ---------------------------------------------------------------------------

/// After the mark: empty the lists, mark the pages unswept, sweep them all.
let collect (h_mark: heap) (st: pstate) : GTot (heap & pstate) =
  SA.sweep_all h_mark (SS.start_sweep st)

/// The whole collection: grey the roots, mark from them, sweep.
let collection (h: heap) (st: pstate) (roots: Seq.seq obj_addr) : GTot (heap & pstate) =
  collect (Mark.mark (D.darken h roots) roots) st

/// What the mark needs, as `GC.Impl.gc_precondition_with_roots` for the
/// unbounded mark (`GC.Spec.Correctness.mark_satisfies_mark_post`).  The
/// same as `D.mark_ready`.
let mark_pre (h_init: heap) (gs roots: Seq.seq obj_addr) : prop =
  MarkInv.mark_inv h_init gs /\ Mark.root_props h_init roots /\
  Mark.no_black_objects h_init /\ Wf.no_pointer_to_blue h_init /\
  (forall (r: obj_addr). Seq.mem r roots <==> Seq.mem r gs) /\
  GP.graph_pre h_init roots

/// ---------------------------------------------------------------------------
/// 1. Safety: nothing reachable is lost
/// ---------------------------------------------------------------------------

/// Every block on a list is free: the large lists are sound (`fls_sound`,
/// as the old clause), and a swept pool page's list holds exactly its free
/// slots (L4).
let lists_sound (g: heap) (st: pstate) : prop =
  FLs.fls_sound g st.large /\
  (forall (i: nat{i < n_pages}). pool_list_ok g st.pm i)

/// The first three conjuncts are the old `gc_safe`'s.  `lists_sound`
/// replaces `fls_sound`.  The last two are new: nothing points to a free
/// block (L10), and the allocator's `Idle` invariant holds again.
let gc_safe_pages (h_init g: heap) (st: pstate) (roots: Seq.seq obj_addr) : prop =
  well_formed_heap g /\
  Corr.full_gc_correctness h_init g roots /\
  Corr.major_gc_live_subgraph_isomorphism h_init g roots /\
  lists_sound g st /\
  Wf.no_pointer_to_blue g /\
  PA.inv I.Idle g st

/// ---------------------------------------------------------------------------
/// 2. Liveness: everything unreachable is reclaimed and reusable
/// ---------------------------------------------------------------------------

/// (a) Every word of every object unreachable before the collection -- its
///     header and its fields -- lies inside a free (blue) block.  The old
///     clause, word for word.
let unreachable_reclaimed (h_init g: heap) (roots: Seq.seq obj_addr) : prop =
  forall (x: obj_addr) (p: nat).
    Seq.mem x (objects zero_addr h_init) /\
    ~(Corr.heap_reachable h_init roots x) /\
    SV.in_extent h_init x p ==>
    SV.blue_covered g p

/// (b) Free memory is listed: every free slot of a swept pool page is on
///     its page's list (L4); every pool page with a free slot is on its
///     class's list (L8); every free block of a swept run of at least
///     `lg_min` words is on the large lists (L9).  Every free page is a
///     `Free` page: no free block of a run holds a whole page (L7, in (c1)).
let free_listed (g: heap) (st: pstate) : prop =
  (forall (i: nat{i < n_pages}). pool_list_ok g st.pm i) /\
  avail_ok st /\
  (forall (y: obj_addr). Seq.mem y (objects zero_addr g) /\ is_blue y g /\ large_listable g st.pm y ==>
     FL.reachable_on_fl g (FLs.fls_head st.large (SC.size_class (U64.v (wosize_of_object y g)))) y)

/// What the sweep keeps and frees, against the marked heap:
///   - every black object survives, white, at its size;
///   - every object that is not free is one of those;
///   - a word of a block of the marked heap is free exactly when the block
///     was not black;
///   - in a swept run, no two free blocks are adjacent and no free block
///     holds a whole page (L7);
///   - a page that is still a pool page holds a live object, so a pool page
///     with no live slot is `Free`.
let lossless (h_mark g: heap) (st: pstate) : prop =
  (forall (x: obj_addr). Seq.mem x (objects zero_addr h_mark) /\ is_black x h_mark ==>
     Seq.mem x (objects zero_addr g) /\ is_white x g /\
     wosize_of_object x g == wosize_of_object x h_mark) /\
  (forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) ==>
     Seq.mem x (objects zero_addr h_mark) /\ is_black x h_mark) /\
  (forall (x: obj_addr) (p: nat). Seq.mem x (objects zero_addr h_mark) /\ SV.in_extent h_mark x p ==>
     (SV.blue_covered g p <==> ~(is_black x h_mark))) /\
  (forall (i: nat{i < n_pages}). run_swept_ok g st.pm i) /\
  (forall (i: nat{i < n_pages}). SPo.pool_live g st i)

/// (c1) No memory is held without cause: the result is the collection of
///      the heap a correct mark left, and the sweep lost nothing.
let sweep_lossless (h_init g: heap) (st: pstate) (roots: Seq.seq obj_addr) : prop =
  exists (h_mark: heap) (st_m: pstate).
    GP.marked h_init h_mark roots /\
    (g, st) == collect h_mark st_m /\
    lossless h_mark g st

/// (c2) No memory is lost: the walk tiles the heap (`well_formed_heap`, and
///      `pages_ok` makes it reach the end), and every block of it is a live
///      object, listed free memory, or one of the bounded kinds of waste of
///      `PT.block_class`.  No fourth class.  `PT.heap_partitioned` states
///      the same as a word count, as the old `heap_partitioned`: the words
///      of each kind sum to the end of the walk.
let heap_classified (g: heap) (st: pstate) : prop =
  forall (y: obj_addr). Seq.mem y (objects zero_addr g) ==> PT.block_class g st y

let gc_live_pages (h_init g: heap) (st: pstate) (roots: Seq.seq obj_addr) : prop =
  unreachable_reclaimed h_init g roots /\
  free_listed g st /\
  sweep_lossless h_init g st roots /\
  heap_classified g st /\
  PT.heap_partitioned g st

/// ---------------------------------------------------------------------------
/// The clauses, one lemma each
/// ---------------------------------------------------------------------------

/// The setting: `g, st` is the collection of `h_mark, st_m`.
let setting (h_init h_mark: heap) (st_m: pstate) (g: heap) (st: pstate) (roots: Seq.seq obj_addr) : prop =
  GP.marked h_init h_mark roots /\ GP.graph_pre h_init roots /\ MP.mark_inv h_mark st_m /\
  (g, st) == collect h_mark st_m

let setting_facts (h_init h_mark: heap) (st_m: pstate) (g: heap) (st: pstate) (roots: Seq.seq obj_addr)
  : Lemma (requires setting h_init h_mark st_m g st roots)
          (ensures SV.swept h_mark (SS.start_sweep st_m) g st /\ pages_ok g st /\ well_formed_heap g /\
                   MP.all_swept st /\ GP.ctx h_init h_mark (SS.start_sweep st_m) g st roots /\
                   objects zero_addr h_mark == objects zero_addr h_init /\
                   (forall (x: obj_addr). Seq.mem x (objects zero_addr h_init) ==>
                      wosize_of_object x h_mark == wosize_of_object x h_init))
  = Corr.mark_post_elim_wfh h_init h_mark roots 0UL;
    Corr.mark_post_elim_no_grey h_init h_mark roots 0UL;
    Corr.mark_post_elim_tri_color h_init h_mark roots 0UL;
    Wf.mark_post_elim_no_pointer_to_blue h_init h_mark roots 0UL;
    Corr.mark_post_elim_objects h_init h_mark roots 0UL;
    Corr.mark_post_elim_wosize h_init h_mark roots 0UL;
    SS.start_ready h_mark st_m;
    SV.swept_of h_mark (SS.start_sweep st_m)

/// (a)
let live_a (h_init h_mark: heap) (st_m: pstate) (g: heap) (st: pstate) (roots: Seq.seq obj_addr)
  : Lemma (requires setting h_init h_mark st_m g st roots)
          (ensures unreachable_reclaimed h_init g roots)
  = setting_facts h_init h_mark st_m g st roots;
    Corr.mark_post_elim_black_reachable h_init h_mark roots 0UL;
    let one (x: obj_addr) (p: nat)
      : Lemma (requires Seq.mem x (objects zero_addr h_init) /\ ~(Corr.heap_reachable h_init roots x) /\
                        SV.in_extent h_init x p)
              (ensures SV.blue_covered g p)
      = HeapModel.graph_vertices_mem h_init x;
        SV.dead_covered h_mark (SS.start_sweep st_m) g st x p
    in
    FStar.Classical.forall_intro_2 (fun x -> FStar.Classical.move_requires (one x))

/// (b) and the lists' soundness, from `pages_ok`.
let lists (g: heap) (st: pstate)
  : Lemma (requires pages_ok g st)
          (ensures free_listed g st /\ lists_sound g st /\ Wf.no_pointer_to_blue g /\
                   (forall (i: nat{i < n_pages}). run_swept_ok g st.pm i))
  = GC.Spec.Pages.Step.pages_ok_elim g st

/// (c1)
let live_c1 (h_init h_mark: heap) (st_m: pstate) (g: heap) (st: pstate) (roots: Seq.seq obj_addr)
  : Lemma (requires setting h_init h_mark st_m g st roots)
          (ensures sweep_lossless h_init g st roots)
  = setting_facts h_init h_mark st_m g st roots;
    let st0 = SS.start_sweep st_m in
    lists g st;
    let kept (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr h_mark) /\ is_black x h_mark ==>
               Seq.mem x (objects zero_addr g) /\ is_white x g /\
               wosize_of_object x g == wosize_of_object x h_mark)
      = if Seq.mem x (objects zero_addr h_mark) && is_black x h_mark then
          SV.black_survives h_mark st0 g st x
    in
    FStar.Classical.forall_intro kept;
    let surv (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) ==>
               Seq.mem x (objects zero_addr h_mark) /\ is_black x h_mark)
      = if Seq.mem x (objects zero_addr g) && not (is_blue x g) then SV.survivor h_mark st0 g st x
    in
    FStar.Classical.forall_intro surv;
    let word (x: obj_addr) (p: nat)
      : Lemma (Seq.mem x (objects zero_addr h_mark) /\ SV.in_extent h_mark x p ==>
               (SV.blue_covered g p <==> ~(is_black x h_mark)))
      = if Seq.mem x (objects zero_addr h_mark) &&
           FStar.IndefiniteDescription.strong_excluded_middle (SV.in_extent h_mark x p) then begin
          if is_black x h_mark then SV.live_uncovered h_mark st0 g st x p
          else SV.dead_covered h_mark st0 g st x p
        end
    in
    FStar.Classical.forall_intro_2 word;
    SS.start_ready h_mark st_m;
    SPo.sweep_all_pools h_mark st0;
    assert (lossless h_mark g st)

/// The block at a walk position of a page, by the page's kind.
let classify_page (g: heap) (st: pstate) (y: obj_addr) (j: nat{j < n_pages})
  : Lemma (requires shape_ok g st.pm /\ MP.all_swept st /\ is_blue y g /\
                    steps_to g (U64.v zero_addr) (U64.v y - 8) /\
                    page_base j <= U64.v y - 8 /\ U64.v y - 8 < page_base (j + 1))
          (ensures PT.block_class g st y)
  = let b = U64.v y - 8 in
    hd_address_spec y;
    R.hdr_obj g y;
    is_blue_iff y g;
    let reached ()
      : Lemma (requires walk_page st.pm j) (ensures steps_to g (page_base j) b)
      = walk_pages_reached g st.pm j;
        R.steps_to_det g (U64.v zero_addr) (page_base j) b
    in
    assert (page_shape g st.pm j);
    match (entry st.pm j).kind with
    | Free ->
      reached ();
      MP.free_page_only g j b
    | Pool c ->
      reached ();
      ST.slot0 j c;
      ST.pool_pos3 g j c 0 b
    | LargeHead n ->
      page_base_mono (j + 1) (j + n);
      assert (in_swept_run st.pm b)
    | LargeCont ->
      assert (cont_ok st.pm j);
      eliminate exists (u: nat{u < n_pages}). u < j /\ in_run st.pm u j
      with begin
        page_base_mono u j;
        page_base_mono (j + 1) (u + run_len (entry st.pm u).kind);
        assert (in_swept_run st.pm b)
      end

/// (c2)
let live_c2 (g: heap) (st: pstate)
  : Lemma (requires pages_ok g st /\ MP.all_swept st /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==> is_white x g \/ is_blue x g))
          (ensures heap_classified g st /\ PT.heap_partitioned g st)
  = GC.Spec.Pages.Step.pages_ok_elim g st;
    let one (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g)) (ensures PT.block_class g st y)
      = if is_blue y g then begin
          let b = U64.v y - 8 in
          hd_address_spec y;
          R.obj_iff g y;
          if b >= pages_end then begin
            pages_end_bound ();
            page_base_aligned n_pages;
            walk_pages_reached g st.pm n_pages;
            R.steps_to_det g (U64.v zero_addr) pages_end b;
            if b > pages_end then begin
              steps_to_refl g pages_end;
              R.block_before g pages_end pages_end b
            end
          end else begin
            steps_to_le g (U64.v zero_addr) b;
            page_of_spec b;
            classify_page g st y (page_of b)
          end
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one);
    heap_tiled g st.pm;
    PT.partitioned g st

/// ---------------------------------------------------------------------------
/// 3. The theorems
/// ---------------------------------------------------------------------------

/// **For any mark** that leaves `GP.marked` and the allocator's marking
/// invariant.
let gc_correct_gen (h_init h_mark: heap) (st_m: pstate) (roots: Seq.seq obj_addr)
  : Lemma (requires GP.marked h_init h_mark roots /\ GP.graph_pre h_init roots /\ MP.mark_inv h_mark st_m)
          (ensures (let (g, st) = collect h_mark st_m in
                    gc_safe_pages h_init g st roots /\ gc_live_pages h_init g st roots))
  = let (g, st) = collect h_mark st_m in
    let st0 = SS.start_sweep st_m in
    setting_facts h_init h_mark st_m g st roots;
    GP.pillars h_init h_mark st0 g st roots;
    GP.iso h_init h_mark st0 g st roots;
    lists g st;
    live_a h_init h_mark st_m g st roots;
    live_c1 h_init h_mark st_m g st roots;
    let colour (x: obj_addr)
      : Lemma (Seq.mem x (objects zero_addr g) ==> is_white x g \/ is_blue x g)
      = if Seq.mem x (objects zero_addr g) && not (is_blue x g) then SV.survivor h_mark st0 g st x
    in
    FStar.Classical.forall_intro colour;
    live_c2 g st

/// The mark's facts about the darkened heap, restated about the first heap:
/// the two differ only in the roots' colours.
let marked_of_darkened (h hd hm: heap) (roots: Seq.seq obj_addr)
  : Lemma (requires D.kept h hd roots /\ Corr.mark_post hd hm roots 0UL /\
                    well_formed_heap h /\ Mark.no_black_objects h /\ Wf.no_pointer_to_blue h /\
                    (forall (x: obj_addr) (i: U64.t).
                       Seq.mem x (objects zero_addr hd) /\ U64.v i >= 1 /\
                       U64.v i <= U64.v (wosize_of_object x hd) ==>
                       GC.Spec.HeapGraph.get_field hm x i == GC.Spec.HeapGraph.get_field hd x i))
          (ensures GP.marked h hm roots)
  = Corr.mark_post_elim_wfh hd hm roots 0UL;
    Corr.mark_post_elim_no_grey hd hm roots 0UL;
    Corr.mark_post_elim_objects hd hm roots 0UL;
    Corr.mark_post_elim_density hd hm roots 0UL;
    Corr.mark_post_elim_objects_gt0 hd hm roots 0UL;
    Wf.mark_post_elim_no_pointer_to_blue hd hm roots 0UL;
    Corr.mark_post_elim_tri_color hd hm roots 0UL;
    Corr.mark_post_elim_black_reachable hd hm roots 0UL;
    Corr.mark_post_elim_graph hd hm roots 0UL;
    Corr.mark_post_elim_wosize hd hm roots 0UL;
    Corr.mark_post_elim_blue hd hm roots 0UL;
    Corr.mark_post_intro h hm roots 0UL

/// The mark from the darkened roots leaves what `gc_correct_gen` needs, from
/// the `Idle` invariant.
let mark_ok (h_init: heap) (st: pstate) (roots: Seq.seq obj_addr)
  : Lemma (requires D.start_pre h_init st roots)
          (ensures (let hm = Mark.mark (D.darken h_init roots) roots in
                    GP.marked h_init hm roots /\ MP.mark_inv hm st))
  = let hd = D.darken h_init roots in
    let hm = Mark.mark hd roots in
    D.darken_ok h_init st roots;
    MarkInv.mark_inv_elim_wfh hd roots;
    MarkInv.mark_inv_elim_sp hd roots;
    Corr.mark_satisfies_mark_post hd roots roots 0UL;
    let fld (x: obj_addr) (i: U64.t)
      : Lemma (Seq.mem x (objects zero_addr hd) /\ U64.v i >= 1 /\
               U64.v i <= U64.v (wosize_of_object x hd) ==>
               GC.Spec.HeapGraph.get_field hm x i == GC.Spec.HeapGraph.get_field hd x i)
      = if Seq.mem x (objects zero_addr hd) && U64.v i >= 1 &&
           U64.v i <= U64.v (wosize_of_object x hd) then
          Mark.mark_preserves_get_field hd roots x i
    in
    FStar.Classical.forall_intro_2 fld;
    marked_of_darkened h_init hd hm roots;
    MS.mark_keeps_inv hd st roots

/// **`gc_correct` for pages.**  From the allocator's `Idle` invariant and
/// live roots, the collection -- grey the roots, mark, sweep -- is safe and
/// live.
let gc_correct_pages (h_init: heap) (st: pstate) (roots: Seq.seq obj_addr)
  : Lemma (requires D.start_pre h_init st roots)
          (ensures (let (g, st') = collection h_init st roots in
                    gc_safe_pages h_init g st' roots /\ gc_live_pages h_init g st' roots))
  = mark_ok h_init st roots;
    gc_correct_gen h_init (Mark.mark (D.darken h_init roots) roots) st roots

/// **Why the roots are greyed first.**  `Idle` and `mark_pre` on the same
/// heap allow no root and an empty stack: every live object is white, and
/// the mark needs its roots grey or black and its stack grey.
let idle_mark_pre_empty (h: heap) (st: pstate) (gs roots: Seq.seq obj_addr)
  : Lemma (requires PA.inv I.Idle h st /\ mark_pre h gs roots)
          (ensures Seq.length roots == 0 /\ Seq.length gs == 0)
  = MarkInv.mark_inv_elim_sp h gs;
    let none (r: obj_addr)
      : Lemma (requires Seq.mem r roots \/ Seq.mem r gs) (ensures False)
      = colors_exhaustive_and_exclusive r h;
        D.idle_white h st r
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires none);
    if Seq.length roots > 0 then Seq.contains_cons (Seq.head roots) (Seq.tail roots) (Seq.head roots);
    if Seq.length roots > 0 then Seq.cons_head_tail roots;
    if Seq.length gs > 0 then Seq.contains_cons (Seq.head gs) (Seq.tail gs) (Seq.head gs);
    if Seq.length gs > 0 then Seq.cons_head_tail gs

/// ---------------------------------------------------------------------------
/// 4. The cycle
/// ---------------------------------------------------------------------------

/// One allocation through the interface in `Idle`, then the caller's
/// writes to the new object's fields; nothing on failure.
let allocated (g: heap) (st: pstate) (wz: nat) (g'': heap) : prop =
  let (g', _, o) = PA.alloc I.Idle g st wz in
  (o == 0UL /\ g'' == g') \/
  (o =!= 0UL /\ U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
   I.fields_written g' g'' o)

let alloc_state (g: heap) (st: pstate) (wz: nat) : GTot pstate =
  let (_, s, _) = PA.alloc I.Idle g st wz in s

/// The states the sequential collector and its allocator reach from the
/// empty heap of pages.
noeq type reach : heap -> pstate -> Type =
  | Start : g:heap -> reach (Init.init_heap g) Init.init_state
  | Alloc : #g:heap -> #st:pstate -> reach g st -> wz:nat -> g'':heap ->
            squash (allocated g st wz g'') -> reach g'' (alloc_state g st wz)
  | Collect : #g:heap -> #st:pstate -> reach g st -> roots:Seq.seq obj_addr ->
              squash (D.roots_ok g roots) ->
              reach (fst (collection g st roots)) (snd (collection g st roots))

/// One allocation keeps the `Idle` invariant (`I.allocator_ok`).
let alloc_keeps (g: heap) (st: pstate) (wz: nat) (g'': heap)
  : Lemma (requires PA.inv I.Idle g st /\ allocated g st wz g'')
          (ensures PA.inv I.Idle g'' (alloc_state g st wz))
  = PA.pages_allocator_ok ();
    let (g', s', o) = PA.alloc I.Idle g st wz in
    assert (PA.pages_allocator.I.inv I.Idle g st);
    assert (PA.pages_allocator.I.alloc I.Idle g st wz == (g', s', o));
    assert (I.alloc_post PA.pages_allocator I.Idle g st wz g' s' o)

/// **Every state of the cycle is in the `Idle` invariant.**
let rec reach_inv (#g: heap) (#st: pstate) (r: reach g st)
  : Lemma (ensures PA.inv I.Idle g st) (decreases r)
  = match r with
    | Start g0 -> GC.Spec.Pages.Alloc.init_alloc_pre g0
    | Alloc #g1 #st1 r1 wz g'' _ -> reach_inv r1; alloc_keeps g1 st1 wz g''
    | Collect #g1 #st1 r1 roots _ -> reach_inv r1; gc_correct_pages g1 st1 roots

/// **Every collection of the cycle is correct.**
let cycle_correct (#g: heap) (#st: pstate) (r: reach g st) (roots: Seq.seq obj_addr)
  : Lemma (requires D.roots_ok g roots)
          (ensures (let (g', st') = collection g st roots in
                    gc_safe_pages g g' st' roots /\ gc_live_pages g g' st' roots))
  = reach_inv r;
    gc_correct_pages g st roots

/// The phases of one collection, through the interface (`I.phase_ok`):
/// `Idle` gives `Marking`; greying the roots and the mark keep `Marking`;
/// clearing and the sweep give `Idle` back.
let phases (g: heap) (st: pstate) (roots: Seq.seq obj_addr)
  : Lemma (requires PA.inv I.Idle g st /\ D.roots_ok g roots)
          (ensures (let hd = D.darken g roots in
                    let hm = Mark.mark hd roots in
                    PA.inv I.Marking g st /\ PA.inv I.Marking hd st /\ PA.inv I.Marking hm st /\
                    PA.inv I.Idle (fst (collect hm st)) (snd (collect hm st))))
  = let hd = D.darken g roots in
    PA.pages_allocator_ok ();
    MP.mark_inv_of_ok g st;
    D.darken_ok g st roots;
    mark_ok g st roots;
    gc_correct_pages g st roots

/// ---------------------------------------------------------------------------
/// Vacuity
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"
/// The hypotheses of `gc_correct_pages` are not refutable (the constructive
/// witness is `GC.Spec.Pages.Vacuity.gc_correct_pages_witness`).
[@@expect_failure [19]]
let gc_correct_pages_hyps_not_false (h_init: heap) (st: pstate) (roots: Seq.seq obj_addr)
  : Lemma (requires D.start_pre h_init st roots) (ensures False)
  = ()

/// Nor are those of `gc_correct_gen`.
[@@expect_failure [19]]
let gc_correct_gen_hyps_not_false (h_init h_mark: heap) (st_m: pstate) (roots: Seq.seq obj_addr)
  : Lemma (requires GP.marked h_init h_mark roots /\ GP.graph_pre h_init roots /\ MP.mark_inv h_mark st_m)
          (ensures False)
  = ()

/// Nor is the setting of the sweep lemmas (`GC.Spec.Pages.Survive`).
[@@expect_failure [19]]
let swept_not_false (g0: heap) (st0: pstate) (g: heap) (st: pstate)
  : Lemma (requires SV.swept g0 st0 g st) (ensures False)
  = ()

/// Liveness does not follow from safety alone.
[@@expect_failure [19]]
let gc_live_not_from_safe (h_init g: heap) (st: pstate) (roots: Seq.seq obj_addr)
  : Lemma (requires gc_safe_pages h_init g st roots) (ensures gc_live_pages h_init g st roots)
  = ()
#pop-options

/// Clause (a) has a non-empty guard: an object's header word is in its
/// extent (as `GC.Impl.Correct.unreachable_reclaimed_header`).
let unreachable_reclaimed_header (h_init g: heap) (roots: Seq.seq obj_addr) (x: obj_addr)
  : Lemma (requires unreachable_reclaimed h_init g roots /\
                    Seq.mem x (objects zero_addr h_init) /\ ~(Corr.heap_reachable h_init roots x))
          (ensures SV.blue_covered g (U64.v (hd_address x)))
  = assert (whsize h_init x >= 1);
    assert (SV.next_pos h_init x >= U64.v (hd_address x) + U64.v mword);
    assert (SV.in_extent h_init x (U64.v (hd_address x)))

/// The cycle is not empty: it starts at the empty heap of pages, where an
/// allocation succeeds.
let reach_start (g: heap) : reach (Init.init_heap g) Init.init_state = Start g
