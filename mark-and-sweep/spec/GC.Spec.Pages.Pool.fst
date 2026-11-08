/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Pool - allocating a small block
/// ---------------------------------------------------------------------------
///
/// A small block of `w = wz + 1` words, header included, goes in a slot of
/// class `c = class_of w`:
///   - `pop`: the first page on `avail[c]` gives its first free slot.  The
///     slot gets the object, with its fields cleared, and a blue filler for
///     the rest of the slot.  The page's list loses its head; a page left
///     with no free slot leaves `avail[c]`;
///   - `acquire`: when `avail[c]` is empty, a free page becomes a page of
///     class `c` with every slot free (`GC.Spec.Pages.PoolInit`), and goes on
///     `avail[c]`;
///   - otherwise there is no room.
///
/// `small_alloc_ok` proves `cleared_ok` of the result.

module GC.Spec.Pages.Pool

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
module Mark = GC.Spec.Mark
module PI = GC.Spec.Pages.PoolInit
module Init = GC.Spec.Pages.Init

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The specification
/// ---------------------------------------------------------------------------

let avail_at (st: pstate) (c: nat) : U64.t =
  if c < Seq.length st.avail then Seq.index st.avail c else 0UL

let set_avail (st: pstate) (c: nat) (v: U64.t) : Seq.seq U64.t =
  if c < Seq.length st.avail then Seq.upd st.avail c v else st.avail

/// The slot of page `i` whose list entry is `s`.
let slot_of (i: nat) (c: nat{c < n_cls}) (s: U64.t) : nat =
  cls_bounds c;
  if U64.v s >= page_base i + 8 then (U64.v s - 8 - page_base i) / (cls c * 8) else 0

let small_wz (wz: nat) (c: nat{c < n_cls}) : prop = wz + 1 <= cls c /\ cls c < pow2 54

let small_wz_intro (wz: nat) (c: nat{c < n_cls})
  : Lemma (requires wz + 1 <= cls c) (ensures small_wz wz c)
  = cls_bounds c;
    FStar.Math.Lemmas.pow2_lt_compat 54 20

/// Slot `k` of page `p` takes a filler, then an object of wosize `wz`; `clr`
/// says whether its fields are cleared (`GC.Spec.Pages.Blocks.put_obj_as`).
let fill_slot_as (clr: bool) (g: heap) (p: nat) (c: nat{c < n_cls}) (k: nat) (wz: nat{small_wz wz c})
  : GTot heap =
  cls_bounds c;
  FStar.Math.Lemmas.pow2_lt_compat 54 20;
  let a = slot_base p c k in
  let g1 = if wz + 1 < cls c then put_blue g (a + (wz + 1) * 8) (cls c - (wz + 1)) else g in
  put_obj_as clr g1 a wz

let fill_slot (g: heap) (p: nat) (c: nat{c < n_cls}) (k: nat) (wz: nat{small_wz wz c}) : GTot heap =
  fill_slot_as true g p c k wz

/// Take the first free slot of the first page on `avail[c]`.
let pop_as (clr: bool) (g: heap) (st: pstate) (c: nat{c < n_cls}) (wz: nat{small_wz wz c})
  : GTot (heap & pstate & U64.t)
  = let hd = avail_at st c in
    if hd = 0UL || U64.v hd - 1 >= n_pages then (g, st, 0UL)
    else begin
      let p : nat = U64.v hd - 1 in
      let e = entry st.pm p in
      let k = slot_of p c e.free_head in
      if k >= n_slots c || e.nfree = 0 then (g, st, 0UL)
      else begin
        let nx = hdr g (slot_obj p c k) in
        let e' = { e with free_head = nx; nfree = e.nfree - 1 } in
        let st' = { st with pm = Seq.upd st.pm p e';
                            avail = (if e.nfree = 1 then set_avail st c e.next else st.avail) } in
        PI.slot_fits p c k;
        (fill_slot_as clr g p c k wz, st', U64.uint_to_t (slot_obj p c k))
      end
    end

let pop (g: heap) (st: pstate) (c: nat{c < n_cls}) (wz: nat{small_wz wz c})
  : GTot (heap & pstate & U64.t)
  = pop_as true g st c wz

/// The first free page from `i` on, or `n_pages`.
let rec find_free (pm: page_map) (i: nat) : Tot nat (decreases (if i < n_pages then n_pages - i else 0)) =
  if i >= n_pages then n_pages
  else if (entry pm i).kind = Free then i
  else find_free pm (i + 1)

/// Page `i`, free, becomes a page of class `c` with every slot free, first on
/// `avail[c]`.
let acq_entry (st: pstate) (i: nat{i < n_pages}) (c: nat{c < n_cls}) : page_info =
  { PI.pool_entry i c with next = avail_at st c }

let acq_state (st: pstate) (i: nat{i < n_pages}) (c: nat{c < n_cls}) : pstate =
  assert (i + 1 <= heap_size);
  { st with pm = Seq.upd st.pm i (acq_entry st i c);
            avail = set_avail st c (U64.uint_to_t (i + 1)) }

let acquire (g: heap) (st: pstate) (i: nat{i < n_pages}) (c: nat{c < n_cls}) : GTot (heap & pstate) =
  (PI.pool_init g i c, acq_state st i c)

let small_alloc_as (clr: bool) (g: heap) (st: pstate) (wz: nat{wz + 1 <= small_max}) : GTot (heap & pstate & U64.t) =
  let c = class_of (wz + 1) in
  class_of_fits (wz + 1);
  small_wz_intro wz c;
  if avail_at st c <> 0UL then pop_as clr g st c wz
  else begin
    let i = find_free st.pm 0 in
    if i >= n_pages then (g, st, 0UL)
    else begin
      let (g1, st1) = acquire g st i c in
      pop_as clr g1 st1 c wz
    end
  end

let small_alloc (g: heap) (st: pstate) (wz: nat{wz + 1 <= small_max}) : GTot (heap & pstate & U64.t) =
  small_alloc_as true g st wz

/// The allocator's heap is the cleared one without the clearing
/// (`GC.Spec.Pages.Blocks.clears`).
let pop_clears (g: heap) (st: pstate) (c: nat{c < n_cls}) (wz: nat{small_wz wz c})
  : Lemma (let (gr, sr, o) = pop_as false g st c wz in
           let (gc, sc, oc) = pop_as true g st c wz in
           sc == sr /\ oc == o /\ clears gr gc o wz)
  = let hd = avail_at st c in
    if hd = 0UL || U64.v hd - 1 >= n_pages then ()
    else begin
      let p : nat = U64.v hd - 1 in
      let e = entry st.pm p in
      let k = slot_of p c e.free_head in
      if k >= n_slots c || e.nfree = 0 then ()
      else begin
        PI.slot_fits p c k;
        cls_bounds c;
        FStar.Math.Lemmas.pow2_lt_compat 54 20;
        let a = slot_base p c k in
        let g1 = if wz + 1 < cls c then put_blue g (a + (wz + 1) * 8) (cls c - (wz + 1)) else g in
        put_obj_clears g1 a wz (U64.uint_to_t (slot_obj p c k))
      end
    end

let small_alloc_clears (g: heap) (st: pstate) (wz: nat{wz + 1 <= small_max /\ wz < pow2 54})
  : Lemma (let (gr, sr, o) = small_alloc_as false g st wz in
           let (gc, sc, oc) = small_alloc_as true g st wz in
           sc == sr /\ oc == o /\ clears gr gc o wz)
  = let c = class_of (wz + 1) in
    class_of_fits (wz + 1);
    small_wz_intro wz c;
    if avail_at st c <> 0UL then pop_clears g st c wz
    else begin
      let i = find_free st.pm 0 in
      if i >= n_pages then ()
      else begin
        let (g1, st1) = acquire g st i c in
        pop_clears g1 st1 c wz
      end
    end

/// ---------------------------------------------------------------------------
/// Arithmetic
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let mem_cons (j k: nat) (ks: list nat)
  : Lemma (L.mem j (k :: ks) <==> (j == k \/ L.mem j ks))
  = ()
#pop-options

let slot_of_obj (i: nat) (c: nat{c < n_cls}) (k: nat) (s: U64.t)
  : Lemma (requires U64.v s == slot_obj i c k)
          (ensures slot_of i c s == k)
  = cls_bounds c;
    FStar.Math.Lemmas.paren_mul_right k (cls c) 8;
    FStar.Math.Lemmas.cancel_mul_div k (cls c * 8)

/// Two slots do not overlap.
let slots_apart (i: nat) (c: nat{c < n_cls}) (j k: nat)
  : Lemma (requires j <> k)
          (ensures slot_end i c j <= slot_base i c k \/ slot_base i c j >= slot_end i c k)
  = slot_base_succ i c j;
    slot_base_succ i c k;
    if j < k then FStar.Math.Lemmas.lemma_mult_le_right (cls c * 8) (j + 1) k
    else FStar.Math.Lemmas.lemma_mult_le_right (cls c * 8) (k + 1) j

/// A slot lies in its page, and the tail after every slot.
let slot_in (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (page_base i <= slot_base i c k /\ slot_end i c k <= slots_end i c /\
           slots_end i c <= page_base (i + 1) /\ page_base (i + 1) <= heap_size /\
           slot_base i c k % 8 == 0 /\ slot_base i c k + 16 <= slot_end i c k /\
           cls c < pow2 20 /\ pow2 20 < pow2 54)
  = PI.slot_fits i c k;
    slot_in_page i c k;
    cls_bounds c;
    FStar.Math.Lemmas.pow2_lt_compat 54 20

/// Two pages do not overlap.
let pages_apart (i j: nat)
  : Lemma (requires i <> j)
          (ensures page_base (i + 1) <= page_base j \/ page_base i >= page_base (j + 1))
  = if i < j then FStar.Math.Lemmas.lemma_mult_le_right page_bytes (i + 1) j
    else FStar.Math.Lemmas.lemma_mult_le_right page_bytes (j + 1) i

let n_pages_small () : Lemma (n_pages < pow2 64)
  = assert (n_pages <= heap_size)

/// ---------------------------------------------------------------------------
/// The filled slot
/// ---------------------------------------------------------------------------

let fill_read (g: heap) (p: nat{p < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
              (wz: nat{small_wz wz c}) (x: hp_addr)
  : Lemma (let a = slot_base p c k in
           let w = wz + 1 in
           read_word (fill_slot g p c k wz) x ==
           (if U64.v x = a then ohdr wz
            else if w < cls c && U64.v x = a + w * 8 then bhdr (cls c - w)
            else if a < U64.v x && U64.v x < a + w * 8 then 0UL
            else read_word g x))
  = let a = slot_base p c k in
    slot_in p c k;
    if wz + 1 < cls c then begin
      let g1 = put_blue g (a + (wz + 1) * 8) (cls c - (wz + 1)) in
      put_obj_read g1 a wz x;
      wr_read g (a + (wz + 1) * 8) (bhdr (cls c - (wz + 1))) x
    end
    else put_obj_read g a wz x

let fill_kept (g: heap) (p: nat{p < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
              (wz: nat{small_wz wz c})
  : Lemma (forall (x: hp_addr). U64.v x < slot_base p c k \/ U64.v x >= slot_end p c k ==>
             read_word (fill_slot g p c k wz) x == read_word g x)
  = slot_in p c k;
    FStar.Classical.forall_intro (fill_read g p c k wz)

let fill_blocks (g: heap) (p: nat{p < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
                (wz: nat{small_wz wz c})
  : Lemma (let g' = fill_slot g p c k wz in
           let a = slot_base p c k in
           let w = wz + 1 in
           words_at g' a == w /\ color_at g' a == White /\ new_block_ok g' a /\
           (w < cls c ==> words_at g' (a + w * 8) == cls c - w /\
                          color_at g' (a + w * 8) == Blue /\ new_block_ok g' (a + w * 8)) /\
           steps_to g' a (slot_end p c k) /\
           (forall (b: nat). steps_to g' a b /\ b < slot_end p c k ==> new_block_ok g' b))
  = let g' = fill_slot g p c k wz in
    let a = slot_base p c k in
    let w = wz + 1 in
    slot_in p c k;
    let ra = mk_hp_addr a in
    fill_read g p c k wz ra;
    let fields (x: hp_addr) : Lemma (a < U64.v x /\ U64.v x < a + w * 8 ==> read_word g' x == 0UL)
      = fill_read g p c k wz x
    in
    FStar.Classical.forall_intro fields;
    obj_block g' a wz;
    if w < cls c then begin
      aligned_plus_mul8 a w;
      fill_read g p c k wz (mk_hp_addr (a + w * 8));
      blue_block_ok g' (a + w * 8) (cls c - w)
    end;
    two_blocks g' a w (cls c - w)

/// ---------------------------------------------------------------------------
/// What `pop` starts from
/// ---------------------------------------------------------------------------

let pop_ctx (g: heap) (st: pstate) (c: nat{c < n_cls}) (p: nat) (k: nat) (ks ps: list nat) : prop =
  pages_ok g st /\ well_formed_heap g /\
  p < n_pages /\ c < Seq.length st.avail /\ U64.v (avail_at st c) == p + 1 /\
  (entry st.pm p).kind == Pool c /\ (entry st.pm p).swept == true /\
  k < n_slots c /\ U64.v (entry st.pm p).free_head == slot_obj p c k /\ slot_free g p c k /\
  slot_chain g p c (hdr g (slot_obj p c k)) ks /\ L.noRepeats (k :: ks) /\
  (forall (j: nat). j < n_slots c ==> (L.mem j (k :: ks) <==> slot_free g p c j)) /\
  (entry st.pm p).nfree == L.length ks + 1 /\
  page_chain st.pm (entry st.pm p).next ps /\ L.noRepeats (p :: ps) /\
  (forall (q: nat{q < n_pages}). L.mem q (p :: ps) <==> has_free_slot st.pm c q)

#push-options "--fuel 1"
let pop_ctx_of (g: heap) (st: pstate) (c: nat{c < n_cls}) (p: nat) (ps: list nat) (k: nat) (ks: list nat)
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ c < Seq.length st.avail /\
                    page_chain st.pm (Seq.index st.avail c) (p :: ps) /\ L.noRepeats (p :: ps) /\
                    (forall (q: nat{q < n_pages}). L.mem q (p :: ps) <==> has_free_slot st.pm c q) /\
                    p < n_pages /\
                    slot_chain g p c (entry st.pm p).free_head (k :: ks) /\ L.noRepeats (k :: ks) /\
                    (forall (j: nat). j < n_slots c ==> (L.mem j (k :: ks) <==> slot_free g p c j)) /\
                    (entry st.pm p).nfree == L.length (k :: ks))
          (ensures pop_ctx g st c p k ks ps /\ p == U64.v (avail_at st c) - 1)
  = assert (L.mem p (p :: ps));
    assert (has_free_slot st.pm c p)
#pop-options

let pop_ctx_intro (g: heap) (st: pstate) (c: nat{c < n_cls})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ avail_at st c <> 0UL)
          (ensures exists (k: nat) (ks ps: list nat). pop_ctx g st c (U64.v (avail_at st c) - 1) k ks ps)
  = pages_ok_elim g st;
    eliminate exists (ps0: list nat).
      page_chain st.pm (Seq.index st.avail c) ps0 /\ L.noRepeats ps0 /\
      (forall (q: nat{q < n_pages}). L.mem q ps0 <==> has_free_slot st.pm c q)
    with begin
      match ps0 with
      | [] -> assert_norm (page_chain st.pm (Seq.index st.avail c) [] == (Seq.index st.avail c == 0UL))
      | p :: ps ->
        assert_norm (page_chain st.pm (Seq.index st.avail c) (p :: ps) ==
                     (p < n_pages /\ U64.v (Seq.index st.avail c) == p + 1 /\
                      page_chain st.pm (entry st.pm p).next ps));
        assert_norm (L.mem p (p :: ps));
        assert (has_free_slot st.pm c p);
        assert (pool_list_ok g st.pm p);
        eliminate exists (ks0: list nat).
          slot_chain g p c (entry st.pm p).free_head ks0 /\ L.noRepeats ks0 /\
          (forall (k: nat). k < n_slots c ==> (L.mem k ks0 <==> slot_free g p c k)) /\
          (entry st.pm p).nfree == L.length ks0
        with begin
          match ks0 with
          | [] -> assert_norm (L.length #nat [] == 0)
          | k :: ks ->
            pop_ctx_of g st c p ps k ks;
            assert (pop_ctx g st c (U64.v (avail_at st c) - 1) k ks ps)
        end
    end

/// ---------------------------------------------------------------------------
/// `pop` is correct
/// ---------------------------------------------------------------------------

let pop_entry (g: heap) (st: pstate) (c: nat{c < n_cls}) (p: nat{p < n_pages}) (k: nat) : page_info =
  let e = entry st.pm p in
  { e with free_head = hdr g (slot_obj p c k); nfree = (if e.nfree > 0 then e.nfree - 1 else 0) }

let pop_state (g: heap) (st: pstate) (c: nat{c < n_cls}) (p: nat{p < n_pages}) (k: nat) : pstate =
  let e = entry st.pm p in
  { st with pm = Seq.upd st.pm p (pop_entry g st c p k);
            avail = (if e.nfree = 1 then set_avail st c e.next else st.avail) }

let pop_obj (p: nat{p < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c}) : U64.t =
  PI.slot_fits p c k;
  U64.uint_to_t (slot_obj p c k)

let pop_result (g: heap) (st: pstate) (c: nat{c < n_cls}) (p: nat{p < n_pages}) (k: nat{k < n_slots c})
               (wz: nat{small_wz wz c}) : GTot (heap & pstate & U64.t) =
  (fill_slot g p c k wz, pop_state g st c p k, pop_obj p c k)

let pop_is (g: heap) (st: pstate) (c: nat{c < n_cls}) (p: nat) (k: nat) (ks ps: list nat)
           (wz: nat{small_wz wz c})
  : Lemma (requires pop_ctx g st c p k ks ps)
          (ensures pop g st c wz == pop_result g st c p k wz)
  = slot_of_obj p c k (entry st.pm p).free_head

/// The slot is the stretch `pop` replaces.
let pop_replaces (g: heap) (st: pstate) (c: nat{c < n_cls}) (p: nat) (k: nat) (ks ps: list nat)
                 (wz: nat{small_wz wz c})
  : Lemma (requires pop_ctx g st c p k ks ps)
          (ensures replaces g (fill_slot g p c k wz) (slot_base p c k) (slot_end p c k))
  = let g' = fill_slot g p c k wz in
    let a = slot_base p c k in
    let e = slot_end p c k in
    slot_in p c k;
    pages_ok_elim g st;
    assert (page_local g st.pm p);
    assert (pool_shape g p c);
    walk_pages_reached g st.pm p;
    slots_steps g p c k;
    steps_to_trans g z (page_base p) a;
    slot_steps g p c k;
    slot_base_succ p c k;
    fill_kept g p c k wz;
    fill_blocks g p c k wz;
    let old (b: nat) : Lemma (requires steps_to g a b /\ b < e) (ensures color_at g b == Blue)
      = one_block_pos g a b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires old)

/// The chain of the slots left keeps through the fill.
#push-options "--fuel 1"
let rec chain_kept (g g': heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (hd: U64.t) (ks: list nat)
  : Lemma (requires slot_chain g i c hd ks /\
                    (forall (j: nat). L.mem j ks /\ j < n_slots c ==>
                       kept_range g g' (slot_base i c j) (slot_end i c j)))
          (ensures slot_chain g' i c hd ks)
          (decreases ks)
  = match ks with
    | [] -> ()
    | j :: ks' ->
      slot_frame g g' i c j;
      chain_kept g g' i c (hdr g (slot_obj i c j)) ks'
#pop-options

let other_slot_kept (g: heap) (p: nat{p < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
                    (wz: nat{small_wz wz c}) (j: nat)
  : Lemma (requires j <> k /\ j < n_slots c)
          (ensures kept_range g (fill_slot g p c k wz) (slot_base p c j) (slot_end p c j))
  = slots_apart p c j k;
    fill_kept g p c k wz

/// The facts about the page that `pop` reads.
let slot_ctx (g: heap) (pm: page_map) (c: nat{c < n_cls}) (p: nat) (k: nat) (ks: list nat) : prop =
  p < n_pages /\ (entry pm p).kind == Pool c /\ (entry pm p).swept == true /\
  pool_shape g p c /\ pool_white g pm p /\
  k < n_slots c /\ slot_free g p c k /\
  slot_chain g p c (hdr g (slot_obj p c k)) ks /\ not (L.mem k ks) /\ L.noRepeats ks /\
  (forall (j: nat). j < n_slots c ==> (L.mem j (k :: ks) <==> slot_free g p c j)) /\
  (entry pm p).nfree == L.length ks + 1

let slot_ctx_of (g: heap) (st: pstate) (c: nat{c < n_cls}) (p: nat) (k: nat) (ks ps: list nat)
  : Lemma (requires pop_ctx g st c p k ks ps)
          (ensures slot_ctx g st.pm c p k ks)
  = assert_norm (L.noRepeats (k :: ks) == (not (L.mem k ks) && L.noRepeats ks));
    pages_ok_elim g st;
    assert (page_local g st.pm p);
    assert (page_shape g st.pm p);
    assert (pool_white g st.pm p)

/// The slot `pop` fills is used.
let fill_used (g: heap) (p: nat{p < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
              (wz: nat{small_wz wz c})
  : Lemma (let g' = fill_slot g p c k wz in
           slot_used g' p c k /\ ~(slot_free g' p c k) /\ color_at g' (slot_base p c k) == White)
  = let g' = fill_slot g p c k wz in
    let a = slot_base p c k in
    let w = wz + 1 in
    slot_in p c k;
    fill_blocks g p c k wz;
    if w < cls c then aligned_plus_mul8 a w

/// The page of the slot keeps its clauses.
let fill_page (g: heap) (pm: page_map) (c: nat{c < n_cls}) (p: nat) (k: nat) (ks: list nat)
              (wz: nat{small_wz wz c})
  : Lemma (requires slot_ctx g pm c p k ks)
          (ensures (let g' = fill_slot g p c k wz in
                    let e = entry pm p in
                    let e' = { e with free_head = hdr g (slot_obj p c k);
                                      nfree = (if e.nfree > 0 then e.nfree - 1 else 0) } in
                    page_local g' (Seq.upd pm p e') p))
  = let g' = fill_slot g p c k wz in
    let e = entry pm p in
    let e' = { e with free_head = hdr g (slot_obj p c k);
                      nfree = (if e.nfree > 0 then e.nfree - 1 else 0) } in
    let pm' = Seq.upd pm p e' in
    slot_in p c k;
    fill_used g p c k wz;
    let others (j: nat)
      : Lemma (requires j <> k /\ j < n_slots c)
              (ensures (slot_free g' p c j <==> slot_free g p c j) /\
                       (slot_used g' p c j <==> slot_used g p c j) /\
                       color_at g' (slot_base p c j) == color_at g (slot_base p c j))
      = other_slot_kept g p c k wz j;
        slot_frame g g' p c j
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires others);
    (* the tail *)
    fill_kept g p c k wz;
    if tail_words c > 0 then begin
      slots_fill_page p c;
      kept_hdr g g' (slot_end p c k) heap_size (slots_end p c)
    end;
    assert (pool_shape g' p c);
    (* the list *)
    let kept_ks (j: nat) : Lemma (L.mem j ks /\ j < n_slots c ==>
                                  kept_range g g' (slot_base p c j) (slot_end p c j))
      = if L.mem j ks && j < n_slots c then other_slot_kept g p c k wz j
    in
    FStar.Classical.forall_intro kept_ks;
    chain_kept g g' p c (hdr g (slot_obj p c k)) ks;
    let mem_iff (j: nat) : Lemma (j < n_slots c ==> (L.mem j ks <==> slot_free g' p c j))
      = mem_cons j k ks
    in
    FStar.Classical.forall_intro mem_iff;
    assert (pool_list_ok g' pm' p);
    assert (pool_white g' pm' p)

/// Every other page keeps its clauses.
let pop_others (g: heap) (st: pstate) (c: nat{c < n_cls}) (p: nat{p < n_pages}) (k: nat{k < n_slots c})
               (wz: nat{small_wz wz c})
  : Lemma (requires map_ok st.pm /\ (forall (i: nat{i < n_pages}). page_local g st.pm i) /\
                    tail_shape g /\ (entry st.pm p).kind == Pool c)
          (ensures (let g' = fill_slot g p c k wz in
                    let st' = pop_state g st c p k in
                    (forall (j: nat{j < n_pages}). j < p \/ j >= p + 1 ==> page_local g' st'.pm j) /\
                    tail_shape g' /\ map_ok st'.pm))
  = let g' = fill_slot g p c k wz in
    let st' = pop_state g st c p k in
    slot_in p c k;
    fill_kept g p c k wz;
    others_local g g' st.pm st'.pm p (p + 1);
    tail_kept g g' (p + 1);
    map_ok_same_kinds st.pm st'.pm

/// The page lists.
#push-options "--fuel 1 --z3rlimit 40"
let pop_avail (g: heap) (st: pstate) (c: nat{c < n_cls}) (p: nat) (k: nat) (ks ps: list nat)
              (wz: nat{small_wz wz c})
  : Lemma (requires pop_ctx g st c p k ks ps)
          (ensures avail_ok (pop_state g st c p k))
  = let st' = pop_state g st c p k in
    let e = entry st.pm p in
    pages_ok_elim g st;
    assert (Seq.length st'.avail == n_cls);
    let nexts (q: nat{q < n_pages}) : Lemma ((entry st'.pm q).next == (entry st.pm q).next) = () in
    FStar.Classical.forall_intro nexts;
    let free_slot (c': nat{c' < n_cls}) (q: nat{q < n_pages})
      : Lemma (has_free_slot st'.pm c' q ==
               (if q = p && c' = c then e.nfree > 1 else has_free_slot st.pm c' q))
      = ()
    in
    let per (c': nat{c' < n_cls})
      : Lemma (exists (ps': list nat).
                 page_chain st'.pm (Seq.index st'.avail c') ps' /\ L.noRepeats ps' /\
                 (forall (q: nat{q < n_pages}). L.mem q ps' <==> has_free_slot st'.pm c' q))
      = FStar.Classical.forall_intro (free_slot c');
        if c' = c && e.nfree = 1 then begin
          page_chain_frame st.pm st'.pm e.next ps;
          assert (Seq.index st'.avail c == e.next)
        end else begin
          eliminate exists (ps0: list nat).
            page_chain st.pm (Seq.index st.avail c') ps0 /\ L.noRepeats ps0 /\
            (forall (q: nat{q < n_pages}). L.mem q ps0 <==> has_free_slot st.pm c' q)
          with begin
            page_chain_frame st.pm st'.pm (Seq.index st.avail c') ps0;
            assert (Seq.index st'.avail c' == Seq.index st.avail c')
          end
        end
    in
    FStar.Classical.forall_intro per
#pop-options

/// The large lists.
let pop_large (g: heap) (st: pstate) (c: nat{c < n_cls}) (p: nat) (k: nat) (ks ps: list nat)
              (wz: nat{small_wz wz c})
  : Lemma (requires pop_ctx g st c p k ks ps)
          (ensures large_ok (fill_slot g p c k wz) (pop_state g st c p k))
  = let g' = fill_slot g p c k wz in
    let st' = pop_state g st c p k in
    let a = slot_base p c k in
    let e = slot_end p c k in
    slot_in p c k;
    pages_ok_elim g st;
    pop_replaces g st c p k ks ps wz;
    large_ok_lview g st;
    swept_run_same st.pm st'.pm;
    let away (x: nat) : Lemma (a <= x /\ x < e ==> ~(in_swept_run st.pm x))
      = if a <= x && x < e then
          FStar.Classical.move_requires (not_in_run st.pm p) x
    in
    FStar.Classical.forall_intro away;
    lview_away g g' a e st st' (walk g (large_head st) heap_words);
    lview_large_ok g' st' (walk g (large_head st) heap_words)

/// The object `pop` returns.
let pop_object (g: heap) (p: nat{p < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
               (wz: nat{small_wz wz c})
  : Lemma (requires replaces g (fill_slot g p c k wz) (slot_base p c k) (slot_end p c k))
          (ensures (let g' = fill_slot g p c k wz in
                    let obj = pop_obj p c k in
                    obj =!= 0UL /\ U64.v obj >= 8 /\ U64.v obj < heap_size /\ U64.v obj % 8 == 0 /\
                    (let x : obj_addr = obj in
                     Seq.mem x (objects zero_addr g') /\
                     U64.v (wosize_of_object x g') == wz /\
                     is_white x g' /\
                     ~(Seq.mem x (objects zero_addr g) /\ ~(is_blue x g)))))
  = let g' = fill_slot g p c k wz in
    let a = slot_base p c k in
    let e = slot_end p c k in
    slot_in p c k;
    fill_blocks g p c k wz;
    let x : obj_addr = pop_obj p c k in
    hd_address_spec x;
    replaces_frame_prefix g g' a e;
    steps_to_refl g a;
    obj_iff g' x;
    hdr_obj g' x;
    hdr_obj g x;
    is_white_iff x g';
    is_blue_iff x g

/// Unswept pages are left alone.
let pop_unswept (g: heap) (st: pstate) (p: nat{p < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
                (wz: nat{small_wz wz c})
  : Lemma (requires (entry st.pm p).swept == true)
          (ensures unswept_unchanged g (fill_slot g p c k wz) st (pop_state g st c p k))
  = let g' = fill_slot g p c k wz in
    let st' = pop_state g st c p k in
    slot_in p c k;
    fill_kept g p c k wz;
    let unswept (i: nat{i < n_pages})
      : Lemma (not (entry st.pm i).swept ==> entry st'.pm i == entry st.pm i /\ page_kept g g' i)
      = if not (entry st.pm i).swept then pages_apart i p
    in
    FStar.Classical.forall_intro unswept

let all_pages (g: heap) (pm: page_map) (p: nat{p < n_pages})
  : Lemma (requires page_local g pm p /\
                    (forall (j: nat{j < n_pages}). j < p \/ j >= p + 1 ==> page_local g pm j))
          (ensures forall (j: nat{j < n_pages}). page_local g pm j)
  = let aux (j: nat{j < n_pages}) : Lemma (page_local g pm j) = () in
    FStar.Classical.forall_intro aux

/// The invariant after `pop`.
let pop_pages_ok (g: heap) (st: pstate) (c: nat{c < n_cls}) (p: nat) (k: nat) (ks ps: list nat)
                 (wz: nat{small_wz wz c})
  : Lemma (requires pop_ctx g st c p k ks ps)
          (ensures pages_ok (fill_slot g p c k wz) (pop_state g st c p k) /\
                   well_formed_heap (fill_slot g p c k wz) /\
                   others_unchanged g (fill_slot g p c k wz))
  = let g' = fill_slot g p c k wz in
    let st' = pop_state g st c p k in
    pages_ok_elim g st;
    pop_replaces g st c p k ks ps wz;
    replace_ok g g' (slot_base p c k) (slot_end p c k);
    slot_ctx_of g st c p k ks ps;
    fill_page g st.pm c p k ks wz;
    pop_others g st c p k wz;
    all_pages g' st'.pm p;
    pop_avail g st c p k ks ps wz;
    pop_large g st c p k ks ps wz;
    pages_ok_intro g' st'

/// **`pop` is correct.**
let pop_ok (g: heap) (st: pstate) (c: nat{c < n_cls}) (p: nat) (k: nat) (ks ps: list nat)
           (wz: nat{small_wz wz c})
  : Lemma (requires pop_ctx g st c p k ks ps)
          (ensures cleared_ok g (fill_slot g p c k wz) st (pop_state g st c p k) wz (pop_obj p c k) /\
                   pop_obj p c k =!= 0UL)
  = pop_pages_ok g st c p k ks ps wz;
    pop_replaces g st c p k ks ps wz;
    pop_object g p c k wz;
    pop_unswept g st p c k wz

/// ---------------------------------------------------------------------------
/// `acquire` is correct
/// ---------------------------------------------------------------------------

let blue_hdr_tag (w: pos{w < pow2 20})
  : Lemma (getTag (Init.blue_hdr w) == 0UL /\ getColor (Init.blue_hdr w) == Blue)
  = FStar.Math.Lemmas.pow2_lt_compat 54 20;
    FStar.Math.Lemmas.pow2_lt_compat 64 20;
    makeHeader_getTag (U64.uint_to_t (w - 1)) Blue 0UL;
    makeHeader_getColor (U64.uint_to_t (w - 1)) Blue 0UL

/// In a pool page with every slot free, the walk stops only at slot starts
/// and at the tail.
let rec free_pool_pos (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (j: nat) (b: nat)
  : Lemma (requires j <= n_slots c /\ pool_shape g i c /\
                    (forall (k: nat). k < n_slots c ==> slot_free g i c k) /\
                    steps_to g (slot_base i c j) b /\ b < page_base (i + 1))
          (ensures (exists (k: nat). j <= k /\ k < n_slots c /\ b == slot_base i c k) \/
                   (tail_words c > 0 /\ b == slots_end i c))
          (decreases (n_slots c - j))
  = steps_to_le g (slot_base i c j) b;
    slots_fill_page i c;
    if j = n_slots c then begin
      if b > slots_end i c then begin
        if tail_words c > 0 then begin
          steps_to_refl g (slots_end i c);
          block_before g (slots_end i c) (slots_end i c) b
        end
      end
    end
    else if b = slot_base i c j then ()
    else begin
      slot_in i c j;
      steps_to_refl g (slot_base i c j);
      block_before g (slot_base i c j) (slot_base i c j) b;
      slot_base_succ i c j;
      free_pool_pos g i c (j + 1) b
    end

let aligned_gap (x y: nat)
  : Lemma (requires x % 8 == 0 /\ y % 8 == 0 /\ x < y) (ensures x + 8 <= y)
  = FStar.Math.Lemmas.lemma_div_exact x 8;
    FStar.Math.Lemmas.lemma_div_exact y 8;
    FStar.Math.Lemmas.lemma_mult_le_left 8 (x / 8 + 1) (y / 8)

let acq_avail_at (st: pstate) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires Seq.length st.avail == n_cls)
          (ensures U64.v (avail_at (acq_state st i c) c) == i + 1)
  = ()

/// A fresh pool page is a good set of new blocks.
let pool_init_new (g: heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (b: nat)
  : Lemma (requires steps_to (PI.pool_init g i c) (page_base i) b /\ b < page_base (i + 1))
          (ensures new_block_ok (PI.pool_init g i c) b)
  = let g1 = PI.pool_init g i c in
    PI.pool_init_shape g i c;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (PI.pool_init_free g i c));
    free_pool_pos g1 i c 0 b;
    infix_tag_val ();
    cls_bounds c;
    if tail_words c > 0 && b = slots_end i c then begin
      page_base_mono (i + 1) n_pages;
      slot_base_aligned i c (n_slots c);
      let t = mk_hp_addr (slots_end i c) in
      read_write_same (PI.write_slots g i c (n_slots c)) t (PI.tail_filler_hdr c);
      blue_hdr_tag (tail_words c)
    end else begin
      eliminate exists (k: nat). 0 <= k /\ k < n_slots c /\ b == slot_base i c k
      with begin
        PI.pool_init_slot g i c k;
        assert (mk_hp_addr b == PI.slot_hd i c k);
        blue_hdr_tag (cls c)
      end
    end

let acq_replaces (g: heap) (st: pstate) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires pages_ok g st /\ (entry st.pm i).kind == Free)
          (ensures replaces g (PI.pool_init g i c) (page_base i) (page_base (i + 1)))
  = let g1 = PI.pool_init g i c in
    pages_ok_elim g st;
    assert (page_local g st.pm i);
    page_base_mono i (i + 1);
    page_base_mono (i + 1) n_pages;
    walk_pages_reached g st.pm i;
    free_page_steps g i;
    PI.pool_init_ok g i c;
    pool_steps g1 i c;
    FStar.Math.Lemmas.distributivity_add_left i 1 page_bytes;
    let old (b: nat) : Lemma (requires steps_to g (page_base i) b /\ b < page_base (i + 1))
                             (ensures color_at g b == Blue)
      = one_block_pos g (page_base i) b
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires old);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (pool_init_new g i c));
    page_base_aligned i;
    page_base_aligned (i + 1);
    let kept (x: hp_addr) : Lemma (U64.v x < page_base i \/ U64.v x >= page_base (i + 1) ==>
                                   read_word g1 x == read_word g x)
      = if U64.v x < page_base i then aligned_gap (U64.v x) (page_base i)
    in
    FStar.Classical.forall_intro kept;
    assert (steps_to g z (page_base i));
    assert (steps_to g (page_base i) (page_base (i + 1)));
    assert (steps_to g1 (page_base i) (page_base (i + 1)))

/// A free page that becomes a pool page keeps the map well formed.
let acq_map (pm: page_map) (i: nat{i < n_pages}) (e: page_info)
  : Lemma (requires map_ok pm /\ (entry pm i).kind == Free /\ Pool? e.kind /\ e.swept == true)
          (ensures map_ok (Seq.upd pm i e))
  = let pm1 = Seq.upd pm i e in
    let aux (j: nat{j < n_pages}) : Lemma (run_ok pm1 j /\ cont_ok pm1 j /\ free_ok pm1 j)
      = assert (run_ok pm j /\ cont_ok pm j);
        if (entry pm1 j).kind = LargeCont then
          eliminate exists (h: nat{h < n_pages}). h < j /\ in_run pm h j
          with assert (in_run pm1 h j)
    in
    FStar.Classical.forall_intro aux

let acq_page (g: heap) (st: pstate) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (page_local (PI.pool_init g i c) (acq_state st i c).pm i)
  = let g1 = PI.pool_init g i c in
    PI.pool_init_ok g i c;
    FStar.Classical.forall_intro (FStar.Classical.move_requires (PI.pool_init_free g i c))

#push-options "--fuel 1 --z3rlimit 40"
let acq_avail (g: heap) (st: pstate) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires pages_ok g st /\ (entry st.pm i).kind == Free)
          (ensures avail_ok (acq_state st i c))
  = let st1 = acq_state st i c in
    pages_ok_elim g st;
    assert (Seq.length st1.avail == n_cls);
    let free_slot (c': nat{c' < n_cls}) (q: nat{q < n_pages})
      : Lemma (has_free_slot st1.pm c' q == (if q = i then c' = c else has_free_slot st.pm c' q))
      = ()
    in
    let per (c': nat{c' < n_cls})
      : Lemma (exists (ps': list nat).
                 page_chain st1.pm (Seq.index st1.avail c') ps' /\ L.noRepeats ps' /\
                 (forall (q: nat{q < n_pages}). L.mem q ps' <==> has_free_slot st1.pm c' q))
      = FStar.Classical.forall_intro (free_slot c');
        eliminate exists (ps0: list nat).
          page_chain st.pm (Seq.index st.avail c') ps0 /\ L.noRepeats ps0 /\
          (forall (q: nat{q < n_pages}). L.mem q ps0 <==> has_free_slot st.pm c' q)
        with begin
          assert (not (L.mem i ps0));
          page_chain_frame st.pm st1.pm (Seq.index st.avail c') ps0;
          if c' = c then begin
            assert (page_chain st1.pm (Seq.index st1.avail c) (i :: ps0));
            assert (L.noRepeats (i :: ps0))
          end
        end
    in
    FStar.Classical.forall_intro per
#pop-options

let acq_large (g: heap) (st: pstate) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires pages_ok g st /\ (entry st.pm i).kind == Free)
          (ensures large_ok (PI.pool_init g i c) (acq_state st i c))
  = let g1 = PI.pool_init g i c in
    let st1 = acq_state st i c in
    pages_ok_elim g st;
    acq_replaces g st i c;
    large_ok_lview g st;
    swept_run_same st.pm st1.pm;
    let away (x: nat) : Lemma (page_base i <= x /\ x < page_base (i + 1) ==> ~(in_swept_run st.pm x))
      = if page_base i <= x && x < page_base (i + 1) then
          FStar.Classical.move_requires (not_in_run st.pm i) x
    in
    FStar.Classical.forall_intro away;
    lview_away g g1 (page_base i) (page_base (i + 1)) st st1 (walk g (large_head st) heap_words);
    lview_large_ok g1 st1 (walk g (large_head st) heap_words)

/// **`acquire` is correct**: the invariant holds, and nothing that was not
/// free changed.
let acquire_ok (g: heap) (st: pstate) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ (entry st.pm i).kind == Free)
          (ensures (let g1 = PI.pool_init g i c in
                    let st1 = acq_state st i c in
                    pages_ok g1 st1 /\ well_formed_heap g1 /\ step_ok g g1 st st1 /\
                    avail_at st1 c <> 0UL))
  = let g1 = PI.pool_init g i c in
    let st1 = acq_state st i c in
    pages_ok_elim g st;
    acq_replaces g st i c;
    replace_ok g g1 (page_base i) (page_base (i + 1));
    acq_map st.pm i (acq_entry st i c);
    acq_page g st i c;
    page_base_mono (i + 1) n_pages;
    others_local g g1 st.pm st1.pm i (i + 1);
    all_pages g1 st1.pm i;
    tail_kept g g1 (i + 1);
    acq_avail g st i c;
    acq_large g st i c;
    pages_ok_intro g1 st1;
    assert (Seq.length st.avail == n_cls);
    acq_avail_at st i c;
    let unswept (j: nat{j < n_pages})
      : Lemma (not (entry st.pm j).swept ==> entry st1.pm j == entry st.pm j /\ page_kept g g1 j)
      = if not (entry st.pm j).swept then pages_apart j i
    in
    FStar.Classical.forall_intro unswept

/// ---------------------------------------------------------------------------
/// Small blocks
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let rec find_free_spec (pm: page_map) (i: nat)
  : Lemma (ensures (let r = find_free pm i in
                    (r < n_pages ==> (entry pm r).kind == Free) /\
                    (r >= n_pages ==> (forall (j: nat{j < n_pages}). j >= i ==> (entry pm j).kind =!= Free))))
          (decreases (if i < n_pages then n_pages - i else 0))
  = if i >= n_pages then ()
    else if (entry pm i).kind = Free then ()
    else find_free_spec pm (i + 1)
#pop-options

/// An empty `avail[c]`: no page of class `c` has a free slot.
#push-options "--fuel 1"
let avail_empty (g: heap) (st: pstate) (c: nat{c < n_cls})
  : Lemma (requires pages_ok g st /\ avail_at st c == 0UL)
          (ensures forall (p: nat{p < n_pages}). ~(has_free_slot st.pm c p))
  = pages_ok_elim g st;
    eliminate exists (ps0: list nat).
      page_chain st.pm (Seq.index st.avail c) ps0 /\ L.noRepeats ps0 /\
      (forall (q: nat{q < n_pages}). L.mem q ps0 <==> has_free_slot st.pm c q)
    with (match ps0 with [] -> () | _ :: _ -> ())
#pop-options

let pop_any_ok (g: heap) (st: pstate) (c: nat{c < n_cls}) (wz: nat{small_wz wz c})
  : Lemma (requires pages_ok g st /\ well_formed_heap g /\ avail_at st c <> 0UL)
          (ensures (let (g', st', obj) = pop g st c wz in cleared_ok g g' st st' wz obj /\ obj =!= 0UL))
  = pop_ctx_intro g st c;
    let p = U64.v (avail_at st c) - 1 in
    eliminate exists (k: nat) (ks ps: list nat). pop_ctx g st c p k ks ps
    with begin
      pop_is g st c p k ks ps wz;
      pop_ok g st c p k ks ps wz
    end

/// **A small block is allocated correctly.**
let small_alloc_ok (g: heap) (st: pstate) (wz: nat{wz + 1 <= small_max})
  : Lemma (requires pages_ok g st /\ well_formed_heap g)
          (ensures (let (g', st', obj) = small_alloc g st wz in cleared_ok g g' st st' wz obj))
  = let c = class_of (wz + 1) in
    class_of_fits (wz + 1);
    small_wz_intro wz c;
    if avail_at st c <> 0UL then pop_any_ok g st c wz
    else begin
      let i = find_free st.pm 0 in
      find_free_spec st.pm 0;
      if i >= n_pages then avail_empty g st c
      else begin
        acquire_ok g st i c;
        let g1 = PI.pool_init g i c in
        let st1 = acq_state st i c in
        pop_any_ok g1 st1 c wz;
        let (g', st', obj) = pop g1 st1 c wz in
        cleared_ok_compose g g1 g' st st1 st' wz obj
      end
    end
