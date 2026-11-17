/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Graft - the allocator does not read unswept pages
/// ---------------------------------------------------------------------------
///
/// While the collector sweeps incrementally, unswept pages hold dead white
/// objects whose fields may point to blocks already freed in swept pages, so
/// the heap the allocator is given is not well formed (plan §20.4).  This
/// module shows that this does not matter: the allocator reads and writes
/// only words of swept pages (free pages count as swept) and its state.
///
///   - `graft h d pm` is `h` with the words of the pages unswept in `pm`
///     taken from `d`.
///   - **`alloc_graft`**: if `gk` meets the allocator's precondition, then
///     allocating in `graft gk d pm` gives the same state and object as in
///     `gk`, and the result grafted the same way.  Every page swept in
///     `gk`'s map is swept in `pm`.
///
/// So any heap that agrees with a good one off the unswept pages allocates
/// as the good one does (`graft_self`).  The proofs follow
/// `GC.Spec.Pages.Recolour` path by path; where that module avoids the
/// headers it paints because they are not in free blocks, this one avoids
/// unswept pages because every word the allocator touches lies in a swept
/// page or run (`pop_out`, `page_out`, `cell_out`).

module GC.Spec.Pages.Graft

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
open GC.Spec.Pages.Replace

module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot
module HE = GC.Gen.HeapExtensional
module PI = GC.Spec.Pages.PoolInit
module Pool = GC.Spec.Pages.Pool
module LG = GC.Spec.Pages.Large
module NR = GC.Spec.Pages.NewRun
module Cells = GC.Spec.Pages.Cells
module RC = GC.Spec.Pages.Recolour
module A = GC.Spec.Pages.Alloc

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Unswept words
/// ---------------------------------------------------------------------------

/// The word at `a` lies in a page unswept in `pm`.  Sealed: the proofs
/// below only carry it, except `out_pages`.
[@@"opaque_to_smt"]
let uw (pm: page_map) (a: nat) : bool =
  z <= a && a < pages_end && not (entry pm (page_of a)).swept

/// No word of `[lo, hi)` is unswept.
let out_range (pm: page_map) (lo hi: nat) : prop =
  forall (a: nat). lo <= a /\ a < hi ==> not (uw pm a)

/// Every page swept in `pm` is swept in `pm'`.
let swept_sub (pm pm': page_map) : prop =
  forall (j: nat{j < n_pages}). (entry pm j).swept ==> (entry pm' j).swept

/// Pages `i .. i + k - 1`, all swept, hold no unswept word.
let out_pages (pm: page_map) (i k: nat)
  : Lemma (requires i + k <= n_pages /\
                    (forall (j: nat{j < n_pages}). i <= j /\ j < i + k ==> (entry pm j).swept))
          (ensures out_range pm (page_base i) (page_base (i + k)))
  = let one (a: nat) : Lemma (page_base i <= a /\ a < page_base (i + k) ==> not (uw pm a))
      = reveal_opaque (`%uw) uw;
        if page_base i <= a && a < page_base (i + k) then begin
          page_base_mono i (i + k);
          page_base_mono 0 i;
          let j = page_of a in
          page_of_spec a;
          if j < i then page_base_mono (j + 1) i
          else if j >= i + k then page_base_mono (i + k) j
        end
    in
    FStar.Classical.forall_intro one

/// ---------------------------------------------------------------------------
/// Grafting
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec graft_n (h d: heap) (pm: page_map) (n: nat) : GTot heap (decreases n) =
  if n = 0 then h
  else begin
    let acc = graft_n h d pm (n - 1) in
    let a = (n - 1) * 8 in
    if uw pm a then wr acc a (hdr d a) else acc
  end
#pop-options

/// `h` with the unswept words taken from `d`.
let graft (h d: heap) (pm: page_map) : GTot heap = graft_n h d pm heap_words

let word_index (x: hp_addr) (n: nat)
  : Lemma (requires U64.v x / 8 < n /\ ~(U64.v x / 8 < n - 1))
          (ensures U64.v x == (n - 1) * 8)
  = FStar.Math.Lemmas.lemma_div_mod (U64.v x) 8

#push-options "--fuel 1"
let rec graft_n_read (h d: heap) (pm: page_map) (n: nat) (x: hp_addr)
  : Lemma (ensures read_word (graft_n h d pm n) x ==
                   (if uw pm (U64.v x) && U64.v x / 8 < n then read_word d x else read_word h x))
          (decreases n)
  = if n = 0 then ()
    else begin
      graft_n_read h d pm (n - 1) x;
      let a = (n - 1) * 8 in
      let acc = graft_n h d pm (n - 1) in
      if uw pm a then begin
        wr_read acc a (hdr d a) x;
        if U64.v x = a then assert (mk_hp_addr a == x)
      end;
      if U64.v x / 8 < n && not (U64.v x / 8 < n - 1) then word_index x n
    end
#pop-options

let graft_read (h d: heap) (pm: page_map) (x: hp_addr)
  : Lemma (read_word (graft h d pm) x == (if uw pm (U64.v x) then read_word d x else read_word h x))
  = graft_n_read h d pm heap_words x

/// A heap that agrees with `d` off the unswept words is `d`, grafted.
let graft_self (h d: heap) (pm: page_map)
  : Lemma (requires forall (x: hp_addr). not (uw pm (U64.v x)) ==> read_word h x == read_word d x)
          (ensures graft h d pm == d)
  = let aux (b: nat) : Lemma (b < heap_size /\ b % 8 == 0 ==>
                              read_word (graft h d pm) (U64.uint_to_t b) == read_word d (U64.uint_to_t b))
      = if b < heap_size && b % 8 = 0 then graft_read h d pm (U64.uint_to_t b)
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext (graft h d pm) d

/// Grafting commutes with a write to a word that is not unswept.
let graft_write (h d: heap) (pm: page_map) (a: hp_addr) (v: U64.t)
  : Lemma (requires not (uw pm (U64.v a)))
          (ensures graft (write_word h a v) d pm == write_word (graft h d pm) a v)
  = let l = graft (write_word h a v) d pm in
    let r = write_word (graft h d pm) a v in
    let aux (b: nat) : Lemma (b < heap_size /\ b % 8 == 0 ==>
                              read_word l (U64.uint_to_t b) == read_word r (U64.uint_to_t b))
      = if b < heap_size && b % 8 = 0 then begin
          let ba : hp_addr = U64.uint_to_t b in
          graft_read (write_word h a v) d pm ba;
          graft_read h d pm ba;
          if b = U64.v a then begin
            read_write_same h a v;
            read_write_same (graft h d pm) a v
          end else begin
            read_write_different h a ba v;
            read_write_different (graft h d pm) a ba v
          end
        end
    in
    FStar.Classical.forall_intro aux;
    HE.heap_read_word_ext l r

let graft_wr (h d: heap) (pm: page_map) (a: nat) (v: U64.t)
  : Lemma (requires not (uw pm a))
          (ensures graft (wr h a v) d pm == wr (graft h d pm) a v)
  = if a < heap_size && a % 8 = 0 then graft_write h d pm (mk_hp_addr a) v

let graft_hdr (h d: heap) (pm: page_map) (a: nat)
  : Lemma (requires not (uw pm a)) (ensures hdr (graft h d pm) a == hdr h a)
  = if a < heap_size && a % 8 = 0 then graft_read h d pm (mk_hp_addr a)

let graft_word (h d: heap) (pm: page_map) (a: hp_addr)
  : Lemma (requires not (uw pm (U64.v a))) (ensures read_word (graft h d pm) a == read_word h a)
  = graft_read h d pm a

/// ---------------------------------------------------------------------------
/// The pool path
/// ---------------------------------------------------------------------------

/// A swept page holds no unswept word.
let page_out (pm: page_map) (p: nat{p < n_pages})
  : Lemma (requires (entry pm p).swept) (ensures out_range pm (page_base p) (page_base (p + 1)))
  = let one (j: nat{j < n_pages}) : Lemma (p <= j /\ j < p + 1 ==> (entry pm j).swept) = () in
    FStar.Classical.forall_intro one;
    out_pages pm p 1

/// The page `pop` takes from is swept.
let pop_swept (g: heap) (st: pstate) (c: nat{c < n_cls})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ Some? (RC.pop_at st c))
          (ensures (let Some (p, k) = RC.pop_at st c in
                    p < n_pages /\ k < n_slots c /\ (entry st.pm p).swept))
  = let Some (p, k) = RC.pop_at st c in
    Pool.pop_ctx_intro g st c;
    eliminate exists (k': nat) (ks ps: list nat). Pool.pop_ctx g st c p k' ks ps
    with Pool.slot_of_obj p c k' (entry st.pm p).free_head

/// The slot `pop` takes lies in a swept page.
let pop_out (g: heap) (st: pstate) (pm: page_map) (c: nat{c < n_cls})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ swept_sub st.pm pm /\ Some? (RC.pop_at st c))
          (ensures (let Some (p, k) = RC.pop_at st c in
                    p < n_pages /\ k < n_slots c /\
                    out_range pm (slot_base p c k) (slot_base p c k + cls c * 8)))
  = let Some (p, k) = RC.pop_at st c in
    pop_swept g st c;
    page_out pm p;
    slot_in_page p c k;
    slots_fill_page p c

let fill_graft (g d: heap) (pm: page_map)
               (p: nat{p < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
               (wz: nat{Pool.small_wz wz c})
  : Lemma (requires out_range pm (slot_base p c k) (slot_base p c k + cls c * 8))
          (ensures graft (Pool.fill_slot_as false g p c k wz) d pm ==
                   Pool.fill_slot_as false (graft g d pm) p c k wz)
  = cls_bounds c;
    FStar.Math.Lemmas.pow2_lt_compat 54 20;
    let a = slot_base p c k in
    if wz + 1 < cls c then begin
      let f = a + (wz + 1) * 8 in
      let v = bhdr (cls c - (wz + 1)) in
      graft_wr g d pm f v;
      graft_wr (wr g f v) d pm a (ohdr wz)
    end
    else graft_wr g d pm a (ohdr wz)

let pop_graft (g d: heap) (st: pstate) (pm: page_map) (c: nat{c < n_cls}) (wz: nat{Pool.small_wz wz c})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ swept_sub st.pm pm)
          (ensures (let (g', st', o) = Pool.pop_as false g st c wz in
                    Pool.pop_as false (graft g d pm) st c wz == (graft g' d pm, st', o)))
  = match RC.pop_at st c with
    | None -> ()
    | Some (p, k) ->
      pop_out g st pm c;
      cls_bounds c;
      graft_hdr g d pm (slot_obj p c k);
      fill_graft g d pm p c k wz

/// ---------------------------------------------------------------------------
/// Taking a free page
/// ---------------------------------------------------------------------------

/// A free page is swept.
let free_page_out (g: heap) (st: pstate) (pm: page_map) (i: nat{i < n_pages})
  : Lemma (requires pages_ok g st /\ swept_sub st.pm pm /\ (entry st.pm i).kind == Free)
          (ensures out_range pm (page_base i) (page_base (i + 1)))
  = GC.Spec.Pages.Step.pages_ok_elim g st;
    assert (free_ok st.pm i);
    assert ((entry pm i).swept);
    page_out pm i

#push-options "--fuel 1"
let rec write_slots_graft (g d: heap) (pm: page_map)
                          (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k <= n_slots c})
  : Lemma (requires out_range pm (page_base i) (page_base (i + 1)))
          (ensures graft (PI.write_slots g i c k) d pm == PI.write_slots (graft g d pm) i c k)
          (decreases k)
  = if k = 0 then ()
    else begin
      write_slots_graft g d pm i c (k - 1);
      PI.slot_fits i c (k - 1);
      let g1 = PI.write_slots g i c (k - 1) in
      graft_write g1 d pm (PI.slot_hd i c (k - 1)) (PI.slot_hdr c);
      graft_write (write_word g1 (PI.slot_hd i c (k - 1)) (PI.slot_hdr c)) d pm
                  (PI.slot_link i c (k - 1)) (PI.link_val i c (k - 1))
    end
#pop-options

let pool_init_graft (g d: heap) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires out_range pm (page_base i) (page_base (i + 1)))
          (ensures graft (PI.pool_init g i c) d pm == PI.pool_init (graft g d pm) i c)
  = write_slots_graft g d pm i c (n_slots c);
    if tail_words c > 0 then begin
      slots_fill_page i c;
      page_base_mono (i + 1) n_pages;
      slot_base_aligned i c (n_slots c);
      cls_bounds c;
      graft_write (PI.write_slots g i c (n_slots c)) d pm (mk_hp_addr (slots_end i c)) (PI.tail_filler_hdr c)
    end

/// Acquiring a free page keeps every swept page swept.
let acq_sub (st: pstate) (pm: page_map) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires swept_sub st.pm pm /\ (entry st.pm i).kind == Free /\ free_ok st.pm i)
          (ensures swept_sub (Pool.acq_state st i c).pm pm)
  = ()

/// ---------------------------------------------------------------------------
/// Small blocks
/// ---------------------------------------------------------------------------

let small_graft (g d: heap) (st: pstate) (pm: page_map) (wz: nat{wz + 1 <= small_max})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ swept_sub st.pm pm)
          (ensures (let (g', st', o) = Pool.small_alloc_as false g st wz in
                    Pool.small_alloc_as false (graft g d pm) st wz == (graft g' d pm, st', o)))
  = let c = class_of (wz + 1) in
    class_of_fits (wz + 1);
    Pool.small_wz_intro wz c;
    if Pool.avail_at st c <> 0UL then pop_graft g d st pm c wz
    else begin
      let i = Pool.find_free st.pm 0 in
      Pool.find_free_spec st.pm 0;
      if i >= n_pages then ()
      else begin
        free_page_out g st pm i;
        pool_init_graft g d pm i c;
        Pool.acquire_ok g st i c;
        GC.Spec.Pages.Step.pages_ok_elim g st;
        assert (free_ok st.pm i);
        acq_sub st pm i c;
        let g1 = PI.pool_init g i c in
        let st1 = Pool.acq_state st i c in
        pop_graft g1 d st1 pm c wz
      end
    end

/// ---------------------------------------------------------------------------
/// The large list
/// ---------------------------------------------------------------------------

let whsize_graft (g d: heap) (pm: page_map) (c: obj_addr)
  : Lemma (requires not (uw pm (RC.hx c))) (ensures whsize (graft g d pm) c == whsize g c)
  = hd_address_spec c;
    RC.hx_word c;
    graft_word g d pm (hd_address c);
    wosize_of_object_spec c g;
    wosize_of_object_spec c (graft g d pm)

/// A block of a swept run lies in it, and no word of it is unswept.
let run_block_out (g: heap) (st: pstate) (pm: page_map) (y: obj_addr)
  : Lemma (requires shape_ok g st.pm /\ swept_sub st.pm pm /\ Seq.mem y (objects zero_addr g) /\
                    in_swept_run st.pm (RC.hx y))
          (ensures out_range pm (RC.hx y) (RC.hx y + whsize g y * 8))
  = hd_address_spec y;
    obj_iff g y;
    hdr_obj g y;
    eliminate exists (h: nat{h < n_pages}).
      LargeHead? (entry st.pm h).kind /\ (entry st.pm h).swept /\
      page_base h <= RC.hx y /\ RC.hx y < page_base (h + run_len (entry st.pm h).kind)
    with begin
      let n = run_len (entry st.pm h).kind in
      assert (run_ok st.pm h);
      assert (page_shape g st.pm h);
      walk_pages_reached g st.pm h;
      steps_to_det g z (page_base h) (RC.hx y);
      block_before g (page_base h) (RC.hx y) (page_base (h + n));
      out_pages pm h n
    end

/// A cell of list 0 lies in a swept run, with a field.
let cell_out (g: heap) (st: pstate) (pm: page_map) (y: obj_addr)
  : Lemma (requires pages_ok g st /\ swept_sub st.pm pm /\
                    L.mem y (Cells.walk g (Cells.large_head st) heap_words))
          (ensures out_range pm (RC.hx y) (RC.hx y + whsize g y * 8) /\ whsize g y >= 2 /\
                   not (uw pm (RC.hx y)) /\ not (uw pm (U64.v y)))
  = GC.Spec.Pages.Step.pages_ok_elim g st;
    Cells.large_ok_lview g st;
    let cs = Cells.walk g (Cells.large_head st) heap_words in
    Cells.cells_mem g (Cells.large_head st) cs y;
    hd_address_spec y;
    run_block_out g st pm y

#push-options "--fuel 1"
let rec last_mem (l: list obj_addr{Cons? l})
  : Lemma (ensures L.mem (L.last l) l) (decreases l)
  = match l with
    | [_] -> ()
    | _ :: tl -> last_mem tl
#pop-options

let carved_graft (g d: heap) (pm: page_map) (c: obj_addr) (wz: nat{wz < pow2 54})
  : Lemma (requires out_range pm (RC.hx c) (RC.hx c + whsize g c * 8) /\ wz + 1 <= whsize g c)
          (ensures LG.rem_of (graft g d pm) c wz == LG.rem_of g c wz /\
                   LG.obj_of (graft g d pm) c wz == LG.obj_of g c wz /\
                   graft (LG.carved_as false g c wz) d pm == LG.carved_as false (graft g d pm) c wz)
  = whsize_graft g d pm c;
    let h = LG.hd_of c in
    let l = LG.rem_of g c wz in
    if l >= 1 && l <= pow2 54 then begin
      graft_wr g d pm h (bhdr l);
      graft_wr (put_blue g h l) d pm (h + l * 8) (ohdr wz)
    end
    else graft_wr g d pm h (ohdr wz)

let carve_graft (g d: heap) (pm: page_map) (st: pstate) (pre: list obj_addr) (c: obj_addr)
                (wz: nat{wz < pow2 54})
  : Lemma (requires out_range pm (RC.hx c) (RC.hx c + whsize g c * 8) /\ whsize g c >= 2 /\
                    (forall (y: obj_addr). L.mem y pre ==> not (uw pm (U64.v y)) /\ U64.v y <> RC.hx c))
          (ensures (let (g', st', o) = LG.carve_as false g st pre c wz in
                    LG.carve_as false (graft g d pm) st pre c wz == (graft g' d pm, st', o)))
  = whsize_graft g d pm c;
    if whsize g c < wz + 1 then ()
    else if LG.rem_of g c wz >= lg_min then carved_graft g d pm c wz
    else begin
      RC.hx_word c;
      graft_word g d pm (c <: hp_addr);
      let nx = read_word g (c <: hp_addr) in
      let g1 = LG.unlink_heap g st pre nx in
      (match pre with
       | [] -> ()
       | _ -> last_mem pre; graft_wr g d pm (U64.v (L.last pre)) nx);
      assert (graft g1 d pm == LG.unlink_heap (graft g d pm) st pre nx);
      whsize_graft g1 d pm c;
      if Cons? pre then begin
        last_mem pre;
        hd_address_spec c;
        wosize_of_object_spec c g;
        wosize_of_object_spec c g1;
        wr_read g (U64.v (L.last pre)) nx (hd_address c)
      end;
      carved_graft g1 d pm c wz
    end

/// ---------------------------------------------------------------------------
/// A new run
/// ---------------------------------------------------------------------------

let free_run_out (g: heap) (st: pstate) (pm: page_map) (i k: nat)
  : Lemma (requires pages_ok g st /\ swept_sub st.pm pm /\ GC.Spec.Pages.Theorems.free_run st.pm i k)
          (ensures out_range pm (page_base i) (page_base (i + k)))
  = GC.Spec.Pages.Step.pages_ok_elim g st;
    out_pages pm i k

let run_heap_graft (g d: heap) (pm: page_map)
                   (i: nat) (k: pos) (wz: nat{wz < pow2 54}) (hd0: U64.t)
  : Lemma (requires out_range pm (page_base i) (page_base (i + k)) /\ wz + 1 <= k * page_wsize)
          (ensures graft (NR.run_heap_as false g i k wz hd0) d pm ==
                   NR.run_heap_as false (graft g d pm) i k wz hd0)
  = let a = page_base i in
    let w = wz + 1 in
    let r = NR.rest k w in
    RC.page_base_add i k;
    let g1 =
      if r > 0 && r <= pow2 54 then begin
        let g2 = put_blue g (a + w * 8) r in
        graft_wr g d pm (a + w * 8) (bhdr r);
        if r >= lg_min then begin
          graft_wr g2 d pm (a + w * 8 + 8) hd0;
          wr g2 (a + w * 8 + 8) hd0
        end
        else g2
      end
      else g
    in
    graft_wr g1 d pm a (ohdr wz)

/// ---------------------------------------------------------------------------
/// Large blocks
/// ---------------------------------------------------------------------------

/// The list the large path walks is the same in `g` and in `graft g d pm`.
let walks_same (g d: heap) (st: pstate) (pm: page_map)
  : Lemma (requires pages_ok g st /\ swept_sub st.pm pm)
          (ensures (let h = Cells.large_head st in
                    let cs = Cells.walk g h heap_words in
                    Cells.walk (graft g d pm) h heap_words == cs /\
                    (forall (y: obj_addr). L.mem y cs ==> whsize (graft g d pm) y == whsize g y)))
  = let h = Cells.large_head st in
    let cs = Cells.walk g h heap_words in
    let one (y: obj_addr)
      : Lemma (L.mem y cs ==>
                 read_word (graft g d pm) (y <: hp_addr) == read_word g (y <: hp_addr) /\
                 whsize (graft g d pm) y == whsize g y)
      = if L.mem y cs then begin
          cell_out g st pm y;
          graft_word g d pm (y <: hp_addr);
          whsize_graft g d pm y
        end
    in
    FStar.Classical.forall_intro one;
    RC.walk_agree (graft g d pm) g h heap_words

let large_graft (g d: heap) (st: pstate) (pm: page_map) (wz: nat{wz < pow2 54})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ swept_sub st.pm pm)
          (ensures (let (g', st', o) = A.large_alloc_as false g st wz in
                    A.large_alloc_as false (graft g d pm) st wz == (graft g' d pm, st', o)))
  = let h = Cells.large_head st in
    let cs = Cells.walk g h heap_words in
    walks_same g d st pm;
    RC.split_fit_agree (graft g d pm) g cs (wz + 1);
    match LG.split_fit g cs (wz + 1) with
    | Some (pre, c, post) ->
      LG.split_fit_some g cs (wz + 1) pre c post;
      FStar.List.Tot.Properties.append_mem_forall pre (c :: post);
      LG.mem_cons_obj c c post;
      GC.Spec.Pages.Step.pages_ok_elim g st;
      Cells.large_ok_lview g st;
      RC.not_in_pre pre c post;
      Cells.cells_mem g h cs c;
      cell_out g st pm c;
      let one (y: obj_addr) : Lemma (L.mem y pre ==> not (uw pm (U64.v y)) /\ U64.v y <> RC.hx c)
        = if L.mem y pre then begin
            Cells.cells_mem g h cs y;
            cell_out g st pm y;
            RC.link_not_hdr g y c
          end
      in
      FStar.Classical.forall_intro one;
      carve_graft g d pm st pre c wz
    | None ->
      let k = GC.Spec.Pages.Theorems.pages_for (wz + 1) in
      let i = NR.find_run st.pm k 0 in
      NR.find_run_spec st.pm k 0;
      if i + k > n_pages then ()
      else begin
        free_run_out g st pm i k;
        NR.pages_for_spec (wz + 1);
        run_heap_graft g d pm i k wz h
      end

/// ---------------------------------------------------------------------------
/// The allocator
/// ---------------------------------------------------------------------------

/// **The allocator does not read unswept pages.**  If `gk` meets its
/// precondition, allocating in `gk` with the unswept words of `pm` replaced
/// by those of `d` gives the same state and object, and the same heap with
/// those words replaced.
let alloc_graft (gk d: heap) (st: pstate) (pm: page_map) (wz: nat)
  : Lemma (requires pages_ok gk st /\ well_formed_heap gk /\ swept_sub st.pm pm)
          (ensures (let (g', st', o) = A.alloc gk st wz in
                    A.alloc (graft gk d pm) st wz == (graft g' d pm, st', o)))
  = if wz + 1 >= pow2 54 then ()
    else if wz + 1 <= small_max then small_graft gk d st pm wz
    else large_graft gk d st pm wz

/// So a heap `g` that agrees with a good heap `gk` off the unswept pages
/// allocates as `gk` does.
let alloc_agree (gk g: heap) (st: pstate) (wz: nat)
  : Lemma (requires pages_ok gk st /\ well_formed_heap gk /\
                    (forall (x: hp_addr). not (uw st.pm (U64.v x)) ==> read_word gk x == read_word g x))
          (ensures (let (gk', st', o) = A.alloc gk st wz in
                    A.alloc g st wz == (graft gk' g st.pm, st', o)))
  = graft_self gk g st.pm;
    alloc_graft gk g st st.pm wz
