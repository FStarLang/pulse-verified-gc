/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.MidSweep - the page allocator during an incremental sweep
/// ---------------------------------------------------------------------------
///
/// Plan §20.4.  While the collector sweeps page by page, some pages are
/// swept and some are not.  The unswept ones hold the mark's result: black
/// survivors, and dead white objects whose fields may point to blocks
/// already freed in swept pages.
///
///   - **`free_sw pm`**: what counts as free mid-sweep: blue blocks, and
///     white blocks of pages unswept in `pm` (main's `free_incremental c`,
///     with "at or above the cursor" read as "in an unswept page").
///   - **`pages_ok_sw g st`**, the mid-sweep invariant: `pages_ok` without
///     L10 (the shapes; the swept pages' lists, colours and runs; the lists),
///     no grey block in an unswept page, and
///     `well_formed_heap_with (free_sw st.pm) g`.
///   - **`alloc_sw_ok`**: allocation (the `Sweeping` allocator, white) from
///     `pages_ok_sw` gives `alloc_ok`'s guarantees and every heap the caller
///     makes by writing the new object's fields satisfies `pages_ok_sw`, and
///     main's five allocator facts (plan §20.1).
///
/// The proof runs the allocator on a surrogate heap: `g` with the fields of
/// the dead objects of unswept pages cleared (`GC.Spec.Pages.Scrub`).  The
/// surrogate satisfies `pages_ok` and `well_formed_heap`, so `alloc_correct`
/// applies to it, and it agrees with `g` off the unswept pages, which the
/// allocator never reads (`GC.Spec.Pages.Graft`).  The heap the allocator
/// makes from `g` is the one it makes from the surrogate with the dead
/// fields put back.

module GC.Spec.Pages.MidSweep

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

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module G = GC.Spec.Pages.Graft
module Sc = GC.Spec.Pages.Scrub
module NO = GC.Spec.Pages.NewOnly
module A = GC.Spec.Pages.Alloc
module Th = GC.Spec.Pages.Theorems
module F = GC.Spec.Pages.Fill
module R = GC.Spec.Pages.Replace
module Wf = GC.Spec.Pages.Wf
module SW = GC.Spec.Pages.SweepWf
module SPI = GC.Spec.SweepPhase.Intrinsic

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// What counts as free mid-sweep
/// ---------------------------------------------------------------------------

/// The header of `x` lies in a page unswept in `pm`.
let unswept_at (pm: page_map) (x: obj_addr) : bool = G.uw pm (U64.v x - 8)

/// Blue blocks, and white blocks of unswept pages: the sweep frees them.
let free_sw (pm: page_map) : free_def =
  fun g x -> is_blue x g || (is_white x g && unswept_at pm x)

let free_sw_ok (pm: page_map) : Lemma (free_def_ok (free_sw pm))
  = reveal_opaque (`%free_def_ok) free_def_ok;
    let det (g g': heap) (x: obj_addr)
      : Lemma ((is_block g x <==> is_block g' x) /\ read_word g (hd_address x) == read_word g' (hd_address x) ==>
               free_sw pm g x == free_sw pm g' x)
      = if read_word g (hd_address x) = read_word g' (hd_address x) then color_of_header_eq x g g'
    in
    FStar.Classical.forall_intro_3 det

/// A dead object: white, in an unswept page.
let dead (g: heap) (pm: page_map) (z: obj_addr) : GTot bool = is_white z g && unswept_at pm z

/// No grey block in an unswept page (the mark has finished there).
let no_grey_unswept (g: heap) (pm: page_map) : prop =
  (forall (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat).
     (entry pm i).kind == Pool c /\ not (entry pm i).swept /\ k < n_slots c /\ slot_used g i c k ==>
     color_at g (slot_base i c k) =!= Gray) /\
  (forall (h: nat{h < n_pages}) (a: nat).
     LargeHead? (entry pm h).kind /\ not (entry pm h).swept /\ run_block g h (run_len (entry pm h).kind) a ==>
     color_at g a =!= Gray)

/// ---------------------------------------------------------------------------
/// The mid-sweep invariant
/// ---------------------------------------------------------------------------

/// **`pages_ok_sw`** (plan §20.4):
///   - `pages_ok` without L10 (`Scrub.core`): the shapes of every page
///     (L1–L3, L6); the free-slot lists, colours and runs of swept pages
///     (L4, L5, L7); the class lists and the large lists, which hold swept
///     pages and blocks only (L8, L9);
///   - no grey block in an unswept page;
///   - well formed, with free meaning `free_sw`: the fields of every block
///     that is not free point to blocks that are not free, so a dead object
///     of an unswept page may point anywhere.
[@@"opaque_to_smt"]
let pages_ok_sw (g: heap) (st: pstate) : prop =
  Sc.core g st /\ no_grey_unswept g st.pm /\ well_formed_heap_with (free_sw st.pm) g

let pages_ok_sw_elim (g: heap) (st: pstate)
  : Lemma (requires pages_ok_sw g st)
          (ensures Sc.core g st /\ shape_ok g st.pm /\ no_grey_unswept g st.pm /\
                   well_formed_heap_with (free_sw st.pm) g)
  = reveal_opaque (`%pages_ok_sw) pages_ok_sw;
    Sc.core_shape g st

let pages_ok_sw_intro (g: heap) (st: pstate)
  : Lemma (requires Sc.core g st /\ no_grey_unswept g st.pm /\ well_formed_heap_with (free_sw st.pm) g)
          (ensures pages_ok_sw g st)
  = reveal_opaque (`%pages_ok_sw) pages_ok_sw

/// ---------------------------------------------------------------------------
/// Unswept words
/// ---------------------------------------------------------------------------

/// Every word of pages `i .. i + k - 1`, all unswept, is unswept.
let in_pages_uw (pm: page_map) (i k: nat) (a: nat)
  : Lemma (requires i + k <= n_pages /\
                    (forall (j: nat{j < n_pages}). i <= j /\ j < i + k ==> not (entry pm j).swept) /\
                    page_base i <= a /\ a < page_base (i + k))
          (ensures G.uw pm a)
  = reveal_opaque (`%G.uw) G.uw;
    page_base_mono i (i + k);
    page_base_mono 0 i;
    let j = page_of a in
    page_of_spec a;
    if j < i then page_base_mono (j + 1) i
    else if j >= i + k then page_base_mono (i + k) j

/// Every word of an unswept page is unswept.
let page_uw (pm: page_map) (i: nat{i < n_pages}) (a: nat)
  : Lemma (requires not (entry pm i).swept /\ page_base i <= a /\ a < page_base (i + 1))
          (ensures G.uw pm a)
  = let one (j: nat{j < n_pages}) : Lemma (i <= j /\ j < i + 1 ==> not (entry pm j).swept) = () in
    FStar.Classical.forall_intro one;
    in_pages_uw pm i 1 a

/// A heap that keeps the unswept words keeps the unswept pages.
let pages_kept (g g': heap) (pm: page_map)
  : Lemma (requires forall (a: hp_addr). G.uw pm (U64.v a) ==> read_word g' a == read_word g a)
          (ensures forall (i: nat{i < n_pages}). not (entry pm i).swept ==> Th.page_kept g g' i)
  = let page (i: nat{i < n_pages})
      : Lemma (not (entry pm i).swept ==> Th.page_kept g g' i)
      = if not (entry pm i).swept then begin
          let w (a: hp_addr) : Lemma (page_base i <= U64.v a /\ U64.v a < page_base (i + 1) ==>
                                      read_word g' a == read_word g a)
            = if page_base i <= U64.v a && U64.v a < page_base (i + 1) then page_uw pm i (U64.v a)
          in
          FStar.Classical.forall_intro w
        end
    in
    FStar.Classical.forall_intro page

/// The unit a position of the pages lies in, and its swept bit.
let unit_of (g: heap) (pm: page_map) (h: nat)
  : Lemma (requires shape_ok g pm /\ steps_to g R.z h /\ h < pages_end)
          (ensures exists (i: nat{i < n_pages}).
                     walk_page pm i /\ page_base i <= h /\ h < page_base (i + span pm i) /\
                     steps_to g (page_base i) h /\ steps_to g (page_base i) (page_base (i + span pm i)) /\
                     i + span pm i <= n_pages /\
                     (forall (j: nat{j < n_pages}). i <= j /\ j < i + span pm i ==>
                        (entry pm j).swept == (entry pm i).swept))
  = SW.in_unit_lt g pm pm h;
    eliminate exists (i: nat{i < n_pages}).
      walk_page pm i /\ page_base i <= h /\ h < page_base (i + span pm i) /\ steps_to g (page_base i) h
    with begin
      assert (run_ok pm i);
      assert (page_shape g pm i);
      next_walk_page pm i i;
      page_steps g pm i;
      let sw (j: nat{j < n_pages})
        : Lemma (i <= j /\ j < i + span pm i ==> (entry pm j).swept == (entry pm i).swept)
        = ()
      in
      FStar.Classical.forall_intro sw
    end

/// The page of a position.
let page_of_pos (h: nat) (i: nat{i < n_pages}) (k: pos)
  : Lemma (requires page_base i <= h /\ h < page_base (i + k) /\ i + k <= n_pages)
          (ensures U64.v zero_addr <= h /\ h < pages_end /\ i <= page_of h /\ page_of h < i + k)
  = page_base_mono 0 i;
    page_base_mono (i + k) n_pages;
    page_of_spec h;
    let j = page_of h in
    if j < i then page_base_mono (j + 1) i
    else if j >= i + k then page_base_mono (i + k) j

/// **The block of an object of an unswept page is unswept**, header and
/// fields.
let block_uw (g: heap) (pm: page_map) (x: obj_addr) (a: nat)
  : Lemma (requires shape_ok g pm /\ Seq.mem x (objects zero_addr g) /\ unswept_at pm x /\
                    U64.v x - 8 <= a /\ a < F.fields_end g x)
          (ensures G.uw pm a)
  = let h = U64.v x - 8 in
    reveal_opaque (`%G.uw) G.uw;
    R.obj_iff g x;
    R.hdr_obj g x;
    unit_of g pm h;
    eliminate exists (i: nat{i < n_pages}).
      walk_page pm i /\ page_base i <= h /\ h < page_base (i + span pm i) /\
      steps_to g (page_base i) h /\ steps_to g (page_base i) (page_base (i + span pm i)) /\
      i + span pm i <= n_pages /\
      (forall (j: nat{j < n_pages}). i <= j /\ j < i + span pm i ==> (entry pm j).swept == (entry pm i).swept)
    with begin
      let k = span pm i in
      page_of_pos h i k;
      R.block_before g (page_base i) h (page_base (i + k));
      in_pages_uw pm i k a
    end

/// And so is every field of a dead object.
let dead_fields_uw (g: heap) (pm: page_map) (zs: list obj_addr) (a: nat)
  : Lemma (requires shape_ok g pm /\
                    (forall (z: obj_addr). L.mem z zs ==> Seq.mem z (objects zero_addr g) /\ dead g pm z) /\
                    Sc.in_fields g zs a)
          (ensures G.uw pm a)
  = eliminate exists (z: obj_addr). L.mem z zs /\ U64.v z <= a /\ a < F.fields_end g z
    with block_uw g pm z a

/// The interface's unswept words are these.
let unswept_uw (st: pstate) (b: hp_addr)
  : Lemma (GC.Spec.Pages.Allocator.unswept st b <==> G.uw st.pm (U64.v b))
  = reveal_opaque (`%G.uw) G.uw;
    if G.uw st.pm (U64.v b) then page_of_spec (U64.v b);
    let back (i: nat{i < n_pages})
      : Lemma (requires not (entry st.pm i).swept /\ page_base i <= U64.v b /\ U64.v b < page_base (i + 1))
              (ensures G.uw st.pm (U64.v b))
      = page_of_pos (U64.v b) i 1;
        page_of_spec (U64.v b);
        in_page_unique i (page_of (U64.v b)) (U64.v b)
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires back)

/// ---------------------------------------------------------------------------
/// The dead objects and the surrogate heap
/// ---------------------------------------------------------------------------

/// The dead objects of `g`, as a list.
let dead_list (g: heap) (pm: page_map)
  : Ghost (list obj_addr) (requires True)
          (ensures fun zs -> forall (z: obj_addr). L.mem z zs <==> Seq.mem z (objects zero_addr g) /\ dead g pm z)
  = Sc.objects_where g (fun z -> dead g pm z)

let dead_objs (g: heap) (pm: page_map) (zs: list obj_addr)
  : Lemma (requires forall (z: obj_addr). L.mem z zs <==> Seq.mem z (objects zero_addr g) /\ dead g pm z)
          (ensures Sc.objs g zs)
  = let one (z: obj_addr) : Lemma (L.mem z zs ==> ~(is_blue z g))
      = is_white_iff z g; is_blue_iff z g
    in
    FStar.Classical.forall_intro one

/// What counts as free in the surrogate: blue blocks and the dead objects.
let free_z (zs: list obj_addr) : free_def = fun g x -> is_blue x g || L.mem x zs

let free_z_ok (zs: list obj_addr) : Lemma (free_def_ok (free_z zs))
  = reveal_opaque (`%free_def_ok) free_def_ok;
    let det (g g': heap) (x: obj_addr)
      : Lemma ((is_block g x <==> is_block g' x) /\ read_word g (hd_address x) == read_word g' (hd_address x) ==>
               free_z zs g x == free_z zs g' x)
      = if read_word g (hd_address x) = read_word g' (hd_address x) then color_of_header_eq x g g'
    in
    FStar.Classical.forall_intro_3 det

/// The context of the surrogate: `g` mid-sweep, `zs` its dead objects.
let sctx (g: heap) (st: pstate) (zs: list obj_addr) : prop =
  pages_ok_sw g st /\
  (forall (z: obj_addr). L.mem z zs <==> Seq.mem z (objects zero_addr g) /\ dead g st.pm z)

/// The surrogate keeps every block that is not free, block for block.
let surrogate_blocks (g: heap) (st: pstate) (zs: list obj_addr) (x: obj_addr)
  : Lemma (requires sctx g st zs /\ in_use (free_sw st.pm) g x)
          (ensures SPI.same_block g (Sc.scrub g zs) (hd_address x))
  = let gk = Sc.scrub g zs in
    pages_ok_sw_elim g st;
    dead_objs g st.pm zs;
    Sc.scrub_facts g zs;
    hd_address_spec x;
    R.hdr_obj g x;
    let body (a: hp_addr)
      : Lemma (U64.v (hd_address x) < U64.v a /\ U64.v a < GC.Spec.Walk.bnext g (hd_address x) ==>
               read_word gk a == read_word g a)
      = if U64.v (hd_address x) < U64.v a && U64.v a < GC.Spec.Walk.bnext g (hd_address x) then begin
          let none (z: obj_addr) : Lemma (~(L.mem z zs /\ U64.v z <= U64.v a /\ U64.v a < F.fields_end g z))
            = if L.mem z zs then begin
                if z = x then ()
                else F.other_apart g z x
              end
          in
          FStar.Classical.forall_intro none
        end
    in
    FStar.Classical.forall_intro body

/// **The surrogate**: `g` with the fields of its dead objects cleared meets
/// the allocator's precondition, and agrees with `g` off the unswept pages.
#push-options "--z3rlimit 40"
let surrogate (g: heap) (st: pstate) (zs: list obj_addr)
  : Lemma (requires sctx g st zs)
          (ensures (let gk = Sc.scrub g zs in
                    pages_ok gk st /\ well_formed_heap gk /\
                    (forall (x: hp_addr). not (G.uw st.pm (U64.v x)) ==> read_word gk x == read_word g x)))
  = let gk = Sc.scrub g zs in
    let pm = st.pm in
    pages_ok_sw_elim g st;
    dead_objs g pm zs;
    Sc.scrub_facts g zs;
    Sc.core_scrub g zs st;
    (* agreement off the unswept pages *)
    let agree (x: hp_addr) : Lemma (not (G.uw pm (U64.v x)) ==> read_word gk x == read_word g x)
      = if FStar.IndefiniteDescription.strong_excluded_middle (Sc.in_fields g zs (U64.v x))
        then dead_fields_uw g pm zs (U64.v x)
    in
    FStar.Classical.forall_intro agree;
    (* well formed, counting the dead objects free *)
    wf_with_parts ();
    free_sw_ok pm;
    free_z_ok zs;
    let infix (y: obj_addr) : Lemma (Seq.mem y (objects zero_addr gk) ==> ~(is_infix y gk))
      = if Seq.mem y (objects zero_addr gk) then resolve_object_locality y g gk
    in
    FStar.Classical.forall_intro infix;
    assert (no_infix_block gk);
    let same_use (y: obj_addr) : Lemma (in_use (free_z zs) gk y == in_use (free_sw pm) g y)
      = if Seq.mem y (objects zero_addr g) then color_of_header_eq y g gk
    in
    FStar.Classical.forall_intro same_use;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (surrogate_blocks g st zs));
    SPI.wf_transport g gk (free_sw pm) (free_z zs);
    (* and with free meaning blue: the dead objects hold no pointer *)
    let p2 (src dst: obj_addr)
      : Lemma (requires in_use free_stw gk src /\ scannable gk src /\ points_to gk src dst)
              (ensures in_use free_stw gk (resolve_object dst gk))
      = if L.mem src zs then Sc.scrubbed_no_pointer g zs src dst
        else points_to_target_not_free (free_z zs) gk src dst
    in
    pointers_lead_to_non_free_intro free_stw gk p2;
    let p3 (src dst: obj_addr)
      : Lemma (requires in_use free_stw gk src /\ scannable gk src /\ points_to gk src dst)
              (ensures infix_addr_wf gk (objects zero_addr gk) dst)
      = if L.mem src zs then Sc.scrubbed_no_pointer g zs src dst
        else points_to_target_not_free (free_z zs) gk src dst
    in
    interior_pointers_valid_intro free_stw gk p3;
    wf_parts ();
    assert (well_formed_heap gk);
    Wf.wfh_old_parts ();
    Sc.ok_of_core gk st
#pop-options

/// ---------------------------------------------------------------------------
/// Allocation keeps every swept bit
/// ---------------------------------------------------------------------------

let same_swept (pm pm': page_map) : prop =
  forall (j: nat{j < n_pages}). (entry pm' j).swept == (entry pm j).swept

let uw_same (pm pm': page_map) (a: nat)
  : Lemma (requires same_swept pm pm') (ensures G.uw pm' a == G.uw pm a)
  = reveal_opaque (`%G.uw) G.uw

let pop_same (g: heap) (st: pstate) (c: nat{c < n_cls}) (wz: nat{GC.Spec.Pages.Pool.small_wz wz c})
  : Lemma (let (_, st', _) = GC.Spec.Pages.Pool.pop_as false g st c wz in same_swept st.pm st'.pm)
  = ()

let small_same (g: heap) (st: pstate) (wz: nat{wz + 1 <= small_max})
  : Lemma (requires map_ok st.pm)
          (ensures (let (_, st', _) = GC.Spec.Pages.Pool.small_alloc_as false g st wz in same_swept st.pm st'.pm))
  = let c = class_of (wz + 1) in
    class_of_fits (wz + 1);
    GC.Spec.Pages.Pool.small_wz_intro wz c;
    if GC.Spec.Pages.Pool.avail_at st c <> 0UL then pop_same g st c wz
    else begin
      let i = GC.Spec.Pages.Pool.find_free st.pm 0 in
      GC.Spec.Pages.Pool.find_free_spec st.pm 0;
      if i >= n_pages then ()
      else begin
        assert (free_ok st.pm i);
        let st1 = GC.Spec.Pages.Pool.acq_state st i c in
        pop_same (GC.Spec.Pages.PoolInit.pool_init g i c) st1 c wz
      end
    end

let large_same (g: heap) (st: pstate) (wz: nat{wz < pow2 54})
  : Lemma (requires map_ok st.pm)
          (ensures (let (_, st', _) = A.large_alloc_as false g st wz in same_swept st.pm st'.pm))
  = let cs = GC.Spec.Pages.Cells.walk g (GC.Spec.Pages.Cells.large_head st) heap_words in
    match GC.Spec.Pages.Large.split_fit g cs (wz + 1) with
    | Some (pre, c, post) -> ()
    | None ->
      let k = Th.pages_for (wz + 1) in
      let i = GC.Spec.Pages.NewRun.find_run st.pm k 0 in
      GC.Spec.Pages.NewRun.find_run_spec st.pm k 0;
      if i + k > n_pages then ()
      else begin
        GC.Spec.Pages.NewRun.run_entries st.pm i k;
        let one (j: nat{j < n_pages})
          : Lemma ((entry (GC.Spec.Pages.NewRun.run_map st.pm i k) j).swept == (entry st.pm j).swept)
          = if i <= j && j < i + k then assert (free_ok st.pm j)
        in
        FStar.Classical.forall_intro one
      end

/// **Allocation never sweeps or unsweeps a page.**
let alloc_same (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires map_ok st.pm)
          (ensures (let (_, st', _) = A.alloc g st wz in same_swept st.pm st'.pm))
  = if wz + 1 >= pow2 54 then ()
    else if wz + 1 <= small_max then small_same g st wz
    else large_same g st wz

/// ---------------------------------------------------------------------------
/// The new object lies in swept pages
/// ---------------------------------------------------------------------------

let new_out (gk: heap) (st: pstate) (wz: nat) (a: nat)
  : Lemma (requires pages_ok gk st /\ well_formed_heap gk)
          (ensures (let (gk', _, o) = A.alloc gk st wz in
                    o =!= 0UL /\ U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                    U64.v o - 8 <= a /\ a < F.fields_end gk' (o <: obj_addr) ==>
                    not (G.uw st.pm a)))
  = let (gk', st', o) = A.alloc gk st wz in
    if o <> 0UL && U64.v o >= 8 && U64.v o < heap_size && U64.v o % 8 = 0 && wz + 1 < pow2 54 then begin
      let x : obj_addr = o in
      A.alloc_clears gk st wz;
      A.cleared_ok_at gk st wz;
      let (gc, sc, oc) = A.alloc_as true gk st wz in
      hd_address_spec x;
      GC.Spec.Pages.Blocks.zeros_read gk' (U64.v x) wz (hd_address x);
      if U64.v x - 8 <= a && a < F.fields_end gk' x && G.uw st.pm a then begin
        reveal_opaque (`%G.uw) G.uw;
        let i = page_of a in
        page_of_spec a;
        assert (read_word gc (hd_address x) == read_word gk' (hd_address x));
        wosize_of_object_spec x gc;
        wosize_of_object_spec x gk';
        if a < U64.v x then begin
          page_base_aligned i;
          assert (page_base i <= U64.v x - 8);
          GC.Spec.Pages.AllocPhase.hdr_swept gk gc st sc x i
        end
        else A.fields_swept gk gc st sc x i a
      end
    end

/// ---------------------------------------------------------------------------
/// The allocation in `g`, through the surrogate
/// ---------------------------------------------------------------------------

/// Two heaps with the same objects and the same headers.
let same_objs (h1 h2: heap) : prop =
  forall (y: obj_addr).
    (Seq.mem y (objects zero_addr h1) <==> Seq.mem y (objects zero_addr h2)) /\
    (Seq.mem y (objects zero_addr h1) ==> read_word h1 (hd_address y) == read_word h2 (hd_address y))

let same_objs_fill (g: heap) (zs: list obj_addr) (v: hp_addr -> GTot U64.t)
  : Lemma (requires Sc.objs g zs) (ensures same_objs (Sc.fill_objs g zs v) g)
  = Sc.fill_facts g zs v

let in_fields_same (h1 h2: heap) (zs: list obj_addr) (a: nat)
  : Lemma (requires (forall (z: obj_addr). L.mem z zs ==> read_word h1 (hd_address z) == read_word h2 (hd_address z)))
          (ensures Sc.in_fields h1 zs a <==> Sc.in_fields h2 zs a)
  = let one (z: obj_addr) : Lemma (L.mem z zs ==> F.fields_end h1 z == F.fields_end h2 z)
      = if L.mem z zs then begin wosize_of_object_spec z h1; wosize_of_object_spec z h2 end
    in
    FStar.Classical.forall_intro one

/// The words of a heap, as a function.
let reader (h: heap) : hp_addr -> GTot U64.t = fun a -> read_word h a

/// The words of `g'`, from the surrogate's run.
#push-options "--z3rlimit 40"
let alloc_relate (g: heap) (st: pstate) (zs: list obj_addr) (wz: nat)
  : Lemma (requires sctx g st zs)
          (ensures (let gk = Sc.scrub g zs in
                    let (gk', st', o) = A.alloc gk st wz in
                    let (g', st1, o1) = A.alloc g st wz in
                    pages_ok gk st /\ well_formed_heap gk /\ Th.alloc_ok gk gk' st st' wz o /\
                    st1 == st' /\ o1 == o /\ Sc.objs gk' zs /\ Sc.objs g zs /\
                    same_objs gk g /\
                    g' == Sc.fill_objs gk' zs (reader g') /\
                    (o == 0UL ==> g' == g) /\
                    (forall (z: obj_addr). L.mem z zs ==> read_word gk' (hd_address z) == read_word g (hd_address z)) /\
                    (forall (a: hp_addr). G.uw st.pm (U64.v a) ==> read_word g' a == read_word g a) /\
                    (forall (a: hp_addr). ~(Sc.in_fields gk' zs (U64.v a)) ==> read_word g' a == read_word gk' a)))
  = let pm = st.pm in
    let gk = Sc.scrub g zs in
    surrogate g st zs;
    pages_ok_sw_elim g st;
    dead_objs g pm zs;
    Sc.scrub_facts g zs;
    A.alloc_ok_at gk st wz;
    G.alloc_agree gk g st wz;
    let (gk', st', o) = A.alloc gk st wz in
    let g' = G.graft gk' g pm in
    (* the dead objects are kept *)
    let kept (z: obj_addr)
      : Lemma (L.mem z zs ==> Seq.mem z (objects zero_addr gk') /\ ~(is_blue z gk') /\
                              read_word gk' (hd_address z) == read_word g (hd_address z))
      = if L.mem z zs then begin
          color_of_header_eq z g gk;
          color_of_header_eq z gk gk'
        end
    in
    FStar.Classical.forall_intro kept;
    in_fields_same gk' g zs 0;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (in_fields_same gk' g zs));
    (* the words *)
    let uw_word (a: hp_addr) : Lemma (G.uw pm (U64.v a) ==> read_word g' a == read_word g a)
      = G.graft_read gk' g pm a
    in
    FStar.Classical.forall_intro uw_word;
    let other (a: hp_addr) : Lemma (~(Sc.in_fields gk' zs (U64.v a)) ==> read_word g' a == read_word gk' a)
      = G.graft_read gk' g pm a;
        if G.uw pm (U64.v a) && not (FStar.IndefiniteDescription.strong_excluded_middle (Sc.in_fields gk' zs (U64.v a)))
        then begin
          reveal_opaque (`%G.uw) G.uw;
          let i = page_of (U64.v a) in
          page_of_spec (U64.v a);
          assert (Th.page_kept gk gk' i);
          in_fields_same gk' g zs (U64.v a)
        end
    in
    FStar.Classical.forall_intro other;
    let v = reader g' in
    let ext (b: nat) : Lemma (b < heap_size /\ b % 8 == 0 ==>
                              read_word (Sc.fill_objs gk' zs v) (U64.uint_to_t b) == read_word g' (U64.uint_to_t b))
      = if b < heap_size && b % 8 = 0 then Sc.fill_read gk' zs v (U64.uint_to_t b)
    in
    FStar.Classical.forall_intro ext;
    GC.Gen.HeapExtensional.heap_read_word_ext (Sc.fill_objs gk' zs v) g';
    if o = 0UL then G.graft_self gk g pm
#pop-options

/// Every block that is not free in `g` is kept in `g'`, header and fields.
let others_sw (g gk gk' g': heap) (zs: list obj_addr) (pm: page_map) (y: obj_addr)
  : Lemma (requires shape_ok g pm /\ Sc.objs g zs /\ Sc.objs gk' zs /\
                    (forall (z: obj_addr). L.mem z zs ==> unswept_at pm z) /\
                    same_objs gk g /\ same_objs g' gk' /\ Th.others_unchanged gk gk' /\
                    (forall (a: hp_addr). ~(Sc.in_fields g zs (U64.v a)) ==> read_word gk a == read_word g a) /\
                    (forall (z: obj_addr). L.mem z zs ==> read_word gk' (hd_address z) == read_word g (hd_address z)) /\
                    (forall (a: hp_addr). G.uw pm (U64.v a) ==> read_word g' a == read_word g a) /\
                    (forall (a: hp_addr). ~(Sc.in_fields gk' zs (U64.v a)) ==> read_word g' a == read_word gk' a) /\
                    Seq.mem y (objects zero_addr g) /\ ~(is_blue y g))
          (ensures Seq.mem y (objects zero_addr g') /\
                   read_word g' (hd_address y) == read_word g (hd_address y) /\
                   (forall (b: hp_addr). U64.v y <= U64.v b /\
                      U64.v b < U64.v y + U64.v (wosize_of_object y g) * 8 ==>
                      read_word g' b == read_word g b))
  = color_of_header_eq y g gk;
    wosize_of_object_spec y g;
    wosize_of_object_spec y gk;
    let field (b: hp_addr)
      : Lemma (U64.v y <= U64.v b /\ U64.v b < U64.v y + U64.v (wosize_of_object y g) * 8 ==>
               read_word g' b == read_word g b)
      = if U64.v y <= U64.v b && U64.v b < U64.v y + U64.v (wosize_of_object y g) * 8 then begin
          if L.mem y zs then block_uw g pm y (U64.v b)
          else begin
            let none (z: obj_addr)
              : Lemma (~(L.mem z zs /\ U64.v z <= U64.v b /\ U64.v b < F.fields_end g z))
              = if L.mem z zs then F.other_apart g z y
            in
            FStar.Classical.forall_intro none;
            in_fields_same gk' g zs (U64.v b)
          end
        end
    in
    FStar.Classical.forall_intro field

/// **What the allocation does to `g`.**
#push-options "--z3rlimit 40"
let alloc_facts (g: heap) (st: pstate) (zs: list obj_addr) (wz: nat)
  : Lemma (requires sctx g st zs)
          (ensures (let (g', st', o) = A.alloc g st wz in
                    same_swept st.pm st'.pm /\
                    (o == 0UL ==> g' == g /\ st' == st) /\
                    (o =!= 0UL ==>
                       U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                       (let x : obj_addr = o in
                        Seq.mem x (objects zero_addr g') /\ U64.v (wosize_of_object x g') == wz /\
                        is_white x g' /\ ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)) /\
                        (forall (a: nat). U64.v x - 8 <= a /\ a < F.fields_end g' x ==> not (G.uw st.pm a)) /\
                        NO.new_only g g' o)) /\
                    Th.others_unchanged g g' /\ Th.unswept_unchanged g g' st st'))
  = let pm = st.pm in
    let gk = Sc.scrub g zs in
    alloc_relate g st zs wz;
    let (gk', st', o) = A.alloc gk st wz in
    let (g', _, _) = A.alloc g st wz in
    pages_ok_sw_elim g st;
    alloc_same gk st wz;
    Sc.scrub_facts g zs;
    same_objs_fill gk' zs (reader g');
    FStar.Classical.forall_intro (FStar.Classical.move_requires (others_sw g gk gk' g' zs pm));
    pages_kept g g' pm;
    if o <> 0UL then begin
      let x : obj_addr = o in
      NO.alloc_new_only gk st wz;
      color_of_header_eq x g' gk';
      wosize_of_object_spec x g';
      wosize_of_object_spec x gk';
      FStar.Classical.forall_intro (new_out gk st wz);
      let live (y: obj_addr)
        : Lemma (Seq.mem y (objects zero_addr g) ==> (is_blue y g <==> is_blue y gk))
        = if Seq.mem y (objects zero_addr g) then color_of_header_eq y g gk
      in
      FStar.Classical.forall_intro live;
      let only (y: obj_addr)
        : Lemma (Seq.mem y (objects zero_addr g') ==> (is_blue y g' <==> is_blue y gk'))
        = if Seq.mem y (objects zero_addr g') then color_of_header_eq y g' gk'
      in
      FStar.Classical.forall_intro only
    end
#pop-options

/// ---------------------------------------------------------------------------
/// Frames of the mid-sweep clauses
/// ---------------------------------------------------------------------------

/// The pages unswept in `pm'` were unswept in `pm`, with the same entries,
/// and their words are kept: no grey block appears in them.
let no_grey_frame (g g': heap) (pm pm': page_map)
  : Lemma (requires map_ok pm' /\ no_grey_unswept g pm /\
                    (forall (i: nat{i < n_pages}). not (entry pm' i).swept ==> entry pm' i == entry pm i) /\
                    (forall (a: hp_addr). G.uw pm' (U64.v a) ==> read_word g' a == read_word g a))
          (ensures no_grey_unswept g' pm')
  = let pool (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat)
      : Lemma (requires (entry pm' i).kind == Pool c /\ not (entry pm' i).swept /\ k < n_slots c /\ slot_used g' i c k)
              (ensures color_at g' (slot_base i c k) =!= Gray)
      = let w (a: hp_addr) : Lemma (page_base i <= U64.v a /\ U64.v a < page_base (i + 1) ==>
                                    read_word g' a == read_word g a)
          = if page_base i <= U64.v a && U64.v a < page_base (i + 1) then page_uw pm' i (U64.v a)
        in
        FStar.Classical.forall_intro w;
        GC.Spec.Pages.Frame.slot_kept g g' i c k;
        GC.Spec.Pages.Frame.slot_frame g g' i c k
    in
    FStar.Classical.forall_intro_3 (fun i c k -> FStar.Classical.move_requires (pool i c) k);
    let run (h: nat{h < n_pages}) (a: nat)
      : Lemma (requires LargeHead? (entry pm' h).kind /\ not (entry pm' h).swept /\
                        run_block g' h (run_len (entry pm' h).kind) a)
              (ensures color_at g' a =!= Gray)
      = let n = run_len (entry pm' h).kind in
        assert (run_ok pm' h);
        let w (b: hp_addr) : Lemma (page_base h <= U64.v b /\ U64.v b < page_base (h + n) ==>
                                    read_word g' b == read_word g b)
          = if page_base h <= U64.v b && U64.v b < page_base (h + n) then in_pages_uw pm' h n (U64.v b)
        in
        FStar.Classical.forall_intro w;
        GC.Spec.Pages.Frame.run_block_frame g g' h n a
    in
    FStar.Classical.forall_intro_2 (fun h a -> FStar.Classical.move_requires (run h) a)

/// A resolved target of a heap is the same, and as good, once the fields of
/// other objects are rewritten.
#push-options "--z3rlimit 40"
let target_fill (h: heap) (zs: list obj_addr) (v: hp_addr -> GTot U64.t) (t: obj_addr)
  : Lemma (requires Sc.objs h zs /\
                    Seq.mem (resolve_object t h) (objects zero_addr h) /\
                    infix_addr_wf h (objects zero_addr h) t /\
                    ~(L.mem (resolve_object t h) zs))
          (ensures (let h' = Sc.fill_objs h zs v in
                    resolve_object t h' == resolve_object t h /\
                    Seq.mem (resolve_object t h') (objects zero_addr h') /\
                    infix_addr_wf h' (objects zero_addr h') t /\
                    read_word h' (hd_address (resolve_object t h)) == read_word h (hd_address (resolve_object t h))))
  = let h' = Sc.fill_objs h zs v in
    let r = resolve_object t h in
    Sc.fill_facts h zs v;
    hd_address_spec t;
    (* the header of `t` is in the block of `r`, which no field of `zs` meets *)
    let outside (q: nat)
      : Lemma (requires U64.v r - 8 <= q /\ q < F.fields_end h r)
              (ensures ~(Sc.in_fields h zs q))
      = let none (z: obj_addr) : Lemma (~(L.mem z zs /\ U64.v z <= q /\ q < F.fields_end h z))
          = if L.mem z zs then F.other_apart h z r
        in
        FStar.Classical.forall_intro none
    in
    if is_infix t h then begin
      infix_addr_wf_elim h (objects zero_addr h) t;
      let w = U64.v (wosize_of_object t h) in
      let p = U64.v t - w * 8 in
      let pa : obj_addr = U64.uint_to_t p in
      wosize_of_object_spec pa h;
      resolve_infix_spec t h;
      parent_closure_addr_nat_spec t h;
      outside (U64.v t - 8);
      Sc.fill_read h zs v (hd_address t);
      resolve_object_locality t h h';
      resolve_object_locality pa h h';
      infix_addr_wf_transfer h h' (objects zero_addr h) (objects zero_addr h') t
    end else begin
      resolve_non_infix t h;
      outside (U64.v t - 8);
      Sc.fill_read h zs v (hd_address t);
      resolve_object_locality t h h';
      infix_addr_wf_non_infix h' (objects zero_addr h') t
    end
#pop-options
