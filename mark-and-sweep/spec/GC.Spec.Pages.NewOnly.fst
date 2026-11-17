/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.NewOnly - an allocation brings only the new object into use
/// ---------------------------------------------------------------------------
///
/// Main's cycle proofs use that an allocation makes no block but the new one
/// non-free (`MarkPhase.Alloc.alloc_in_use`, `SweepPhase.Mutator.alloc_in_use`,
/// plan §20.1, fact 2).  For the page allocator, `alloc_correct` gives the
/// other half (every block that was not free is kept, `others_unchanged`);
/// this module gives this half.
///
/// **`alloc_new_only`**: from `pages_ok` and `well_formed_heap`, every block
/// of the heap the allocator makes that is not free, other than the new
/// object, was a block that was not free before.
///
/// Every step of the allocator replaces a stretch of free blocks
/// (`GC.Spec.Pages.Replace.replaces`); outside the stretch the walk is kept,
/// and inside it the blocks are the new object and free blocks: a slot and
/// its filler (`fill_blocks`), a new pool page of free slots
/// (`PoolInit.pool_init_free`), a free block and the object carved from its
/// end (`Large.carve_layout`), a run and its free rest (`NewRun.run_layout`),
/// or a free block with a new link (`Large.link_replaces`).  The proof
/// follows `Pool.small_alloc_ok` and `Large.carve_ok` on the cleared
/// allocator, and carries the result to the allocator by `Blocks.clears`.

module GC.Spec.Pages.NewOnly

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
open GC.Spec.Pages.Replace
open GC.Spec.Pages.Cells
open GC.Spec.Pages.Blocks
open GC.Spec.Pages.Step
open GC.Spec.Pages.Theorems

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module PI = GC.Spec.Pages.PoolInit
module Pool = GC.Spec.Pages.Pool
module LG = GC.Spec.Pages.Large
module NR = GC.Spec.Pages.NewRun
module A = GC.Spec.Pages.Alloc
module F = GC.Spec.Pages.Fill
module Wf = GC.Spec.Pages.Wf

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// Every block of `g'` that is not free, other than `o`, was a block of `g`
/// that was not free.
let new_only (g g': heap) (o: U64.t) : prop =
  forall (y: obj_addr). Seq.mem y (objects zero_addr g') /\ ~(is_blue y g') /\ U64.v y <> U64.v o ==>
    Seq.mem y (objects zero_addr g) /\ ~(is_blue y g)

let new_only_trans (g g1 g': heap) (o: U64.t)
  : Lemma (requires new_only g g1 0UL /\ new_only g1 g' o) (ensures new_only g g' o)
  = ()

let new_only_refl (g: heap) (o: U64.t) : Lemma (new_only g g o) = ()

/// The colour of a block, from its header word.
let blue_at (g: heap) (y: obj_addr)
  : Lemma (is_blue y g <==> color_at g (U64.v y - 8) == Blue)
  = hdr_obj g y;
    is_blue_iff y g

/// **A stretch replaced with the new object and free blocks.**
let stretch_new_only (g g': heap) (a e: nat) (o: U64.t)
  : Lemma (requires replaces g g' a e /\
                    (forall (b: nat). steps_to g' a b /\ b < e /\ color_at g' b =!= Blue ==> b + 8 == U64.v o))
          (ensures new_only g g' o)
  = let one (y: obj_addr)
      : Lemma (requires Seq.mem y (objects zero_addr g') /\ ~(is_blue y g') /\ U64.v y <> U64.v o)
              (ensures Seq.mem y (objects zero_addr g) /\ ~(is_blue y g))
      = let h = U64.v y - 8 in
        blue_at g' y;
        blue_at g y;
        hd_address_spec y;
        if h < a || h >= e then begin
          replace_obj_out g g' a e y;
          hdr_obj g y;
          assert (read_word g' (hd_address y) == read_word g (hd_address y))
        end
        else begin
          replaces_frame_prefix g g' a e;
          replace_obj_in g' a e y
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one)

/// No block of the stretch is new and not free.
let stretch_blue (g g': heap) (a e: nat)
  : Lemma (requires replaces g g' a e /\
                    (forall (b: nat). steps_to g' a b /\ b < e ==> color_at g' b == Blue))
          (ensures new_only g g' 0UL)
  = stretch_new_only g g' a e 0UL

/// ---------------------------------------------------------------------------
/// Small blocks
/// ---------------------------------------------------------------------------

/// The blocks of a filled slot: the object, then a free filler.
let fill_pos (g: heap) (p: nat{p < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
             (wz: nat{Pool.small_wz wz c}) (b: nat)
  : Lemma (requires (let g' = Pool.fill_slot g p c k wz in
                     steps_to g' (slot_base p c k) b /\ b < slot_end p c k /\ color_at g' b =!= Blue))
          (ensures b == slot_base p c k)
  = let g' = Pool.fill_slot g p c k wz in
    let a = slot_base p c k in
    let w = wz + 1 in
    Pool.fill_blocks g p c k wz;
    if b <> a then begin
      steps_to_le g' a b;
      steps_to_refl g' a;
      block_before g' a a b;
      let f = a + w * 8 in
      if f < b then begin
        steps_to_refl g' f;
        block_before g' f f b
      end
    end

/// The slot `pop` fills, from its context.
let pop_ctx_new_only (g: heap) (st: pstate) (c: nat{c < n_cls}) (p: nat) (k: nat) (ks ps: list nat)
                     (wz: nat{Pool.small_wz wz c})
  : Lemma (requires Pool.pop_ctx g st c p k ks ps)
          (ensures p < n_pages /\ k < n_slots c /\
                   new_only g (Pool.fill_slot g p c k wz) (Pool.pop_obj p c k))
  = Pool.pop_replaces g st c p k ks ps wz;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (fill_pos g p c k wz));
    stretch_new_only g (Pool.fill_slot g p c k wz) (slot_base p c k) (slot_end p c k) (Pool.pop_obj p c k)

let pop_new_only (g: heap) (st: pstate) (c: nat{c < n_cls}) (wz: nat{Pool.small_wz wz c})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ Pool.avail_at st c <> 0UL)
          (ensures (let (g', _, o) = Pool.pop g st c wz in new_only g g' o))
  = Pool.pop_ctx_intro g st c;
    let p = U64.v (Pool.avail_at st c) - 1 in
    eliminate exists (k: nat) (ks ps: list nat). Pool.pop_ctx g st c p k ks ps
    with begin
      pop_ctx_new_only g st c p k ks ps wz;
      Pool.pop_is g st c p k ks ps wz
    end

/// A new pool page holds free blocks only.
let acq_new_only (g: heap) (st: pstate) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires pages_ok g st /\ (entry st.pm i).kind == Free)
          (ensures new_only g (PI.pool_init g i c) 0UL)
  = let g1 = PI.pool_init g i c in
    Pool.acq_replaces g st i c;
    PI.pool_init_shape g i c;
    FStar.Classical.forall_intro (PI.pool_init_free g i c);
    let one (b: nat)
      : Lemma (requires steps_to g1 (page_base i) b /\ b < page_base (i + 1))
              (ensures color_at g1 b == Blue)
      = assert (slot_base i c 0 == page_base i);
        Pool.free_pool_pos g1 i c 0 b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one);
    stretch_blue g g1 (page_base i) (page_base (i + 1))

let small_new_only (g: heap) (st: pstate) (wz: nat{wz + 1 <= small_max})
  : Lemma (requires pages_ok g st /\ well_formed_heap g)
          (ensures (let (g', _, o) = Pool.small_alloc g st wz in new_only g g' o))
  = let c = class_of (wz + 1) in
    class_of_fits (wz + 1);
    Pool.small_wz_intro wz c;
    if Pool.avail_at st c <> 0UL then pop_new_only g st c wz
    else begin
      let i = Pool.find_free st.pm 0 in
      Pool.find_free_spec st.pm 0;
      if i >= n_pages then new_only_refl g 0UL
      else begin
        Pool.acquire_ok g st i c;
        acq_new_only g st i c;
        let g1 = PI.pool_init g i c in
        let st1 = Pool.acq_state st i c in
        pop_new_only g1 st1 c wz;
        let (g', _, o) = Pool.pop g1 st1 c wz in
        new_only_trans g g1 g' o
      end
    end

/// ---------------------------------------------------------------------------
/// Large blocks
/// ---------------------------------------------------------------------------

let carve_arith (h w wz: nat)
  : Lemma (requires wz + 1 <= w /\ wz >= 1 /\ h + w * 8 <= heap_size)
          (ensures h + (w - (wz + 1)) * 8 + 8 + wz * 8 == h + w * 8 /\
                   h + (w - (wz + 1)) * 8 + 8 < heap_size)
  = FStar.Math.Lemmas.distributivity_sub_left w (wz + 1) 8;
    FStar.Math.Lemmas.distributivity_add_left wz 1 8

/// The carve of a free block that the walk reaches: a free block, then the
/// object.
let carve_new_only (g: heap) (c: obj_addr) (wz: nat{wz < pow2 54})
  : Lemma (requires Seq.mem c (objects zero_addr g) /\ is_blue c g /\ wz + 1 <= whsize g c /\ wz >= 1)
          (ensures new_only g (LG.carved g c wz) (LG.obj_of g c wz))
  = let h : nat = U64.v c - 8 in
    let w = whsize g c in
    let l : nat = w - (wz + 1) in
    hd_address_spec c;
    obj_iff g c;
    hdr_obj g c;
    blue_at g c;
    wosize_of_object_bound c g;
    assert (heap_size < pow2 57);
    FStar.Math.Lemmas.pow2_le_compat 57 54;
    assert (h + w * 8 <= heap_size);
    carve_arith h w wz;
    LG.obj_at_spec (h + l * 8 + 8);
    assert (LG.rem_of g c wz == l);
    assert (U64.v (LG.obj_of g c wz) == h + l * 8 + 8);
    LG.carve_replaces0 g h w wz;
    LG.carve_layout g h l wz;
    stretch_new_only g (LG.carved g c wz) h (h + w * 8) (LG.obj_of g c wz)

/// A new link in a free block keeps every block.
let link_new_only (g: heap) (p: obj_addr) (v: U64.t)
  : Lemma (requires Seq.mem p (objects zero_addr g) /\ is_blue p g /\
                    U64.v (wosize_of_object p g) >= 1 /\ Wf.well_formed_heap_part4 g)
          (ensures new_only g (wr g (U64.v p) v) 0UL)
  = let a = U64.v p - 8 in
    let g1 = wr g (U64.v p) v in
    let e = a + whsize g p * 8 in
    LG.link_replaces g p v;
    hdr_obj g p;
    blue_at g p;
    let one (b: nat)
      : Lemma (requires steps_to g1 a b /\ b < e) (ensures color_at g1 b == Blue)
      = if b <> a then begin
          steps_to_le g1 a b;
          steps_to_refl g1 a;
          block_before g1 a a b
        end
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires one);
    stretch_blue g g1 a e

/// The link word of another free block is not the header of `c`, so `c` is
/// kept with its block.
let link_keeps (g: heap) (p c: obj_addr) (v: U64.t)
  : Lemma (requires Seq.mem p (objects zero_addr g) /\ Seq.mem c (objects zero_addr g) /\ p <> c /\
                    is_blue p g /\ is_blue c g /\ U64.v (wosize_of_object p g) >= 1 /\ Wf.well_formed_heap_part4 g)
          (ensures (let g1 = wr g (U64.v p) v in
                    Seq.mem c (objects zero_addr g1) /\ is_blue c g1 /\ whsize g1 c == whsize g c))
  = let a = U64.v p - 8 in
    let g1 = wr g (U64.v p) v in
    let e = a + whsize g p * 8 in
    LG.link_replaces g p v;
    hd_address_spec c;
    F.other_apart g p c;
    assert (F.fields_end g p == e);
    assert (F.fields_end g c <= a ==> U64.v c - 8 < a);
    assert (U64.v c - 8 < a \/ U64.v c - 8 >= e);
    replace_obj_out g g1 a e c;
    hdr_obj g c;
    assert (read_word g1 (hd_address c) == read_word g (hd_address c));
    color_of_header_eq c g g1;
    wosize_of_object_spec c g;
    wosize_of_object_spec c g1

#push-options "--fuel 1"
let rec last_mem (l: list obj_addr{Cons? l})
  : Lemma (ensures L.mem (L.last l) l) (decreases l)
  = match l with
    | [_] -> ()
    | _ :: tl -> last_mem tl
#pop-options

let large_carve_new_only (g: heap) (st: pstate) (pre: list obj_addr) (c: obj_addr) (post: list obj_addr)
                         (wz: nat{wz < pow2 54})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ lview g st (L.append pre (c :: post)) /\
                    wz + 1 <= whsize g c /\ wz >= 1)
          (ensures (let (g', _, o) = LG.carve g st pre c wz in new_only g g' o))
  = let cs = L.append pre (c :: post) in
    FStar.List.Tot.Properties.append_mem_forall pre (c :: post);
    LG.mem_cons_obj c c post;
    cells_mem g (large_head st) cs c;
    if LG.rem_of g c wz >= lg_min then carve_new_only g c wz
    else begin
      let nx = read_word g (c <: hp_addr) in
      match pre with
      | [] -> carve_new_only g c wz
      | _ ->
        let p = L.last pre in
        let g1 = wr g (U64.v p) nx in
        last_mem pre;
        cells_mem g (large_head st) cs p;
        LG.noRepeats_drop pre c post;
        GC.Spec.Pages.Recolour.not_in_pre pre c post;
        LG.wfh_part4 g;
        link_new_only g p nx;
        link_keeps g p c nx;
        assert (LG.unlink_heap g st pre nx == g1);
        carve_new_only g1 c wz;
        new_only_trans g g1 (LG.carved g1 c wz) (LG.obj_of g1 c wz)
    end

/// A new run: the object, then a free rest.
let run_new_only (g: heap) (st: pstate) (i: nat{i < n_pages}) (k: pos) (wz: nat{wz < pow2 54})
  : Lemma (requires NR.nr_ctx g st i k wz)
          (ensures (let (g', _, o) = NR.new_run g st i k wz in new_only g g' o))
  = NR.nr_rest g st i k wz;
    NR.nr_replaces g st i k wz;
    NR.run_layout g i k wz (large_head st);
    page_base_mono i n_pages;
    LG.obj_at_spec (page_base i + 8);
    let a = page_base i in
    let w = wz + 1 in
    let g' = NR.nr_heap g st i k wz in
    stretch_new_only g g' a (page_base (i + k)) (LG.obj_at (a + 8))

let large_new_only (g: heap) (st: pstate) (wz: nat{wz < pow2 54})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ wz + 1 > small_max)
          (ensures (let (g', _, o) = A.large_alloc_as true g st wz in new_only g g' o))
  = let cs = walk g (large_head st) heap_words in
    pages_ok_elim g st;
    large_ok_lview g st;
    match LG.split_fit g cs (wz + 1) with
    | Some (pre, c, post) ->
      LG.split_fit_some g cs (wz + 1) pre c post;
      large_carve_new_only g st pre c post wz
    | None ->
      let k = pages_for (wz + 1) in
      let i = NR.find_run st.pm k 0 in
      NR.find_run_spec st.pm k 0;
      if i + k > n_pages then new_only_refl g 0UL
      else run_new_only g st i k wz

/// ---------------------------------------------------------------------------
/// The allocator
/// ---------------------------------------------------------------------------

let cleared_new_only (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok g st /\ well_formed_heap g)
          (ensures (let (g', _, o) = A.alloc_as true g st wz in new_only g g' o))
  = if wz + 1 >= pow2 54 then new_only_refl g 0UL
    else if wz + 1 <= small_max then small_new_only g st wz
    else large_new_only g st wz

/// **Only the new object comes into use.**  Every block of the heap the
/// allocator makes that is not free, other than the new object, was a block
/// of the heap before that was not free.
let alloc_new_only (g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok g st /\ well_formed_heap g)
          (ensures (let (g', _, o) = A.alloc g st wz in new_only g g' o))
  = if wz + 1 >= pow2 54 then new_only_refl g 0UL
    else begin
      A.alloc_clears g st wz;
      A.cleared_ok_at g st wz;
      cleared_new_only g st wz;
      let (gr, _, o) = A.alloc g st wz in
      let (gc, _, _) = A.alloc_as true g st wz in
      if o <> 0UL then begin
        let x : obj_addr = o in
        let fr (a: hp_addr)
          : Lemma (U64.v a < U64.v x \/ U64.v a >= F.fields_end gc x ==> read_word gr a == read_word gc a)
          = zeros_read gr (U64.v x) wz a
        in
        FStar.Classical.forall_intro fr;
        let one (y: obj_addr)
          : Lemma (Seq.mem y (objects zero_addr gr) /\ ~(is_blue y gr) /\ U64.v y <> U64.v o ==>
                   Seq.mem y (objects zero_addr g) /\ ~(is_blue y g))
          = F.obj_same gc gr x y;
            if Seq.mem y (objects zero_addr gc) then color_of_header_eq y gc gr
        in
        FStar.Classical.forall_intro one
      end
    end
