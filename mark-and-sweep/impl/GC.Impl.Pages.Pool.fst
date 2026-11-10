/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.Pool - allocation of small blocks, in Pulse
/// ---------------------------------------------------------------------------
///
/// Each function here computes exactly what its specification in
/// `GC.Spec.Pages.Pool` computes, for every heap and state, or, for `pop`
/// and `small_alloc`, for every state with `heads_ready`
/// (`GC.Impl.Pages.Ready`, which the allocator's invariant gives):
///   - the class of a size, the slot size and the slots per page are read
///     from the state's tables (`State.class_at`, `cls_at`, `ns_at`);
///   - `find_free`: the first free page, searched from the free-page hint
///     (no free page lies below it) and leaving the hint at the page found;
///   - `pool_init`: `PoolInit.pool_init`, a free page laid out as slots of a
///     class, each slot linked to the next;
///   - `acquire`: `Pool.acquire`, which also puts the page first on its
///     class's list;
///   - `pop`: `Pool.pop_as false`, the first free slot of the first page on
///     the list, with its filler and header written and its fields left as
///     they were.  As in the prototype and OCaml 5, the slot is the list
///     entry itself: no division and no check, which `heads_ready` makes
///     unneeded;
///   - `small_alloc`: `Pool.small_alloc_as false`.

module GC.Impl.Pages.Pool

#lang-pulse

open Pulse.Lib.Pervasives
open GC.Spec.Pages.Params
open GC.Spec.Pages.Layout
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Impl.Heap
open GC.Impl.Pages.Params
open GC.Impl.Pages.State
open GC.Impl.Pages.Heap

module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq
module R = Pulse.Lib.Reference
module Base = GC.Spec.Base
module SH = GC.Spec.Heap
module Sh = GC.Spec.Pages.Shape
module B = GC.Spec.Pages.Blocks
module PI = GC.Spec.Pages.PoolInit
module P = GC.Spec.Pages.Pool
module Rd = GC.Impl.Pages.Ready

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// Classes and slots
/// ---------------------------------------------------------------------------

/// The largest small block.
let small_max_u64 () : r: U64.t{U64.v r == small_max} = cls_u64 (U64.sub n_cls_u64 1UL)

let tail_words_u64 (c: U64.t{U64.v c < n_cls}) : r: U64.t{U64.v r == tail_words (U64.v c)}
  = cls_bounds (U64.v c);
    U64.rem page_wsize_u64 (cls_u64 c)

/// The start of slot `k` of page `i`, for `k <= n_slots c`.
let slot_base_bound (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k <= n_slots c})
  : Lemma (slot_base i c k <= Base.heap_size /\ slot_base i c k % 8 == 0 /\
           (k < n_slots c ==> slot_base i c k + 16 <= Base.heap_size))
  = slot_base_aligned i c k;
    slots_fill_page i c;
    page_base_mono (i + 1) n_pages;
    if k < n_slots c then PI.slot_fits i c k
    else FStar.Math.Lemmas.lemma_mult_le_right (cls c * 8) k (n_slots c)

let slot_base_u64 (i: U64.t{U64.v i < n_pages}) (c: U64.t{U64.v c < n_cls})
                  (k: U64.t{U64.v k <= n_slots (U64.v c)})
  : r: U64.t{U64.v r == slot_base (U64.v i) (U64.v c) (U64.v k)}
  = slot_base_bound (U64.v i) (U64.v c) (U64.v k);
    page_base_bound (U64.v i);
    cls_bounds (U64.v c);
    FStar.Math.Lemmas.pow2_lt_compat 64 57;
    FStar.Math.Lemmas.lemma_mult_le_right (cls (U64.v c) * 8) (U64.v k) (n_slots (U64.v c));
    U64.add (page_base_u64 i) (U64.mul k (U64.mul (cls_u64 c) 8UL))

/// `slot_base_u64` with the slot size given (read from the table).
inline_for_extraction
let slot_base_cl (i: U64.t{U64.v i < n_pages}) (c: nat{c < n_cls}) (cl: U64.t{U64.v cl == cls c})
                 (k: U64.t{U64.v k <= n_slots c})
  : r: U64.t{U64.v r == slot_base (U64.v i) c (U64.v k)}
  = slot_base_bound (U64.v i) c (U64.v k);
    page_base_bound (U64.v i);
    cls_bounds c;
    FStar.Math.Lemmas.pow2_lt_compat 64 57;
    FStar.Math.Lemmas.lemma_mult_le_right (cls c * 8) (U64.v k) (n_slots c);
    U64.add (page_base_u64 i) (U64.mul k (U64.mul cl 8UL))

/// ---------------------------------------------------------------------------
/// The first free page
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let find_free_step (pm: page_map) (i: nat{i < n_pages})
  : Lemma (P.find_free pm i == (if (entry pm i).kind = Free then i else P.find_free pm (i + 1)))
  = ()

let find_free_end (pm: page_map) : Lemma (P.find_free pm n_pages == n_pages) = ()
#pop-options

let rec find_free_le (pm: page_map) (i: nat)
  : Lemma (ensures P.find_free pm i <= n_pages) (decreases (if i < n_pages then n_pages - i else 0))
  = if i >= n_pages then (assert_norm (P.find_free pm i == (if i >= n_pages then n_pages else 0)))
    else begin find_free_step pm i; find_free_le pm (i + 1) end

/// No page below `h` is free: the search may start at `h`.
let rec find_free_skip (pm: page_map) (j h: nat)
  : Lemma (requires none_free_below pm h /\ j <= h /\ h <= n_pages)
          (ensures P.find_free pm j == P.find_free pm h)
          (decreases (h - j))
  = if j < h then begin find_free_step pm j; find_free_skip pm (j + 1) h end

/// No page below the first free page is free.
let rec find_free_below (pm: page_map) (i: nat)
  : Lemma (requires none_free_below pm i /\ i <= n_pages)
          (ensures none_free_below pm (P.find_free pm i))
          (decreases (n_pages - i))
  = if i < n_pages then begin
      find_free_step pm i;
      if (entry pm i).kind <> Free then find_free_below pm (i + 1)
    end
    else find_free_end pm

fn find_free (t: pstate_t) (#st: erased pstate)
  requires pages_st t st
  returns i: U64.t
  ensures pages_st t st ** pure (U64.v i == P.find_free st.pm 0 /\ U64.v i <= n_pages)
{
  let np = n_pages_u64 ();
  let h = read_hint t;
  find_free_skip st.pm 0 (U64.v h);
  find_free_le st.pm 0;
  let mut i = h;
  let mut go = true;
  while (!go)
    invariant exists* vi vgo.
      R.pts_to i vi ** R.pts_to go vgo ** pages_st t st **
      pure (U64.v vi <= n_pages /\ none_free_below st.pm (U64.v vi) /\
            (vgo ==> P.find_free st.pm (U64.v vi) == P.find_free st.pm 0) /\
            (not vgo ==> U64.v vi == P.find_free st.pm 0))
    decreases ((n_pages - U64.v !i) + (if !go then 1 else 0))
  {
    let vi = !i;
    if (U64.gte vi np) {
      find_free_end st.pm;
      go := false
    } else {
      let r = read_entry t vi;
      find_free_step st.pm (U64.v vi);
      if (is_free_rec r) {
        go := false
      } else {
        i := U64.add vi 1UL
      }
    }
  };
  let vi = !i;
  write_hint t vi;
  vi
}

/// ---------------------------------------------------------------------------
/// A fresh pool page
/// ---------------------------------------------------------------------------

#push-options "--fuel 1"
let write_slots_step (g: Base.heap) (i: nat{i < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c})
  : Lemma (PI.write_slots g i c (k + 1) ==
           SH.write_word (SH.write_word (PI.write_slots g i c k) (PI.slot_hd i c k) (PI.slot_hdr c))
                         (PI.slot_link i c k) (PI.link_val i c k))
  = ()

let write_slots_zero (g: Base.heap) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (PI.write_slots g i c 0 == g)
  = ()
#pop-options

let slot_hdr_u64 (c: U64.t{U64.v c < n_cls}) : r: U64.t{r == PI.slot_hdr (U64.v c)}
  = cls_bounds (U64.v c);
    blue_hdr_u64 (cls_u64 c)

let link_val_u64 (i: U64.t{U64.v i < n_pages}) (c: U64.t{U64.v c < n_cls})
                 (cl: U64.t{U64.v cl == cls (U64.v c)}) (ns: U64.t{U64.v ns == n_slots (U64.v c)})
                 (k: U64.t{U64.v k < n_slots (U64.v c)})
  : r: U64.t{r == PI.link_val (U64.v i) (U64.v c) (U64.v k)}
  = if U64.lt (U64.add k 1UL) ns then begin
      PI.slot_fits (U64.v i) (U64.v c) (U64.v k + 1);
      U64.add (slot_base_cl i (U64.v c) cl (U64.add k 1UL)) 8UL
    end
    else 0UL

let tail_hdr_u64 (c: U64.t{U64.v c < n_cls}) : r: U64.t{r == PI.tail_filler_hdr (U64.v c)}
  = cls_bounds (U64.v c);
    let tw = tail_words_u64 c in
    if U64.gt tw 0UL then blue_hdr_u64 tw else 0UL

fn pool_init (heap: heap_t) (i: U64.t{U64.v i < n_pages}) (c: U64.t{U64.v c < n_cls})
  (cl: U64.t{U64.v cl == cls (U64.v c)}) (ns: U64.t{U64.v ns == n_slots (U64.v c)})
  requires is_heap heap 'g
  ensures is_heap heap (PI.pool_init 'g (U64.v i) (U64.v c))
{
  let h = slot_hdr_u64 c;
  write_slots_zero 'g (U64.v i) (U64.v c);
  let mut k = 0UL;
  while (U64.lt !k ns)
    invariant exists* vk s.
      R.pts_to k vk ** is_heap heap s **
      pure (U64.v vk <= n_slots (U64.v c) /\ s == PI.write_slots 'g (U64.v i) (U64.v c) (U64.v vk))
    decreases (n_slots (U64.v c) - U64.v !k)
  {
    let vk = !k;
    PI.slot_fits (U64.v i) (U64.v c) (U64.v vk);
    let a = slot_base_cl i (U64.v c) cl vk;
    write_word heap a h;
    write_word heap (U64.add a 8UL) (link_val_u64 i c cl ns vk);
    write_slots_step 'g (U64.v i) (U64.v c) (U64.v vk);
    k := U64.add vk 1UL
  };
  let tw = tail_words_u64 c;
  if (U64.gt tw 0UL) {
    slots_fill_page (U64.v i) (U64.v c);
    page_base_mono (U64.v i + 1) n_pages;
    slot_base_aligned (U64.v i) (U64.v c) (n_slots (U64.v c));
    let e = slot_base_u64 i c ns;
    write_word heap e (tail_hdr_u64 c);
    with s. assert (is_heap heap s);
    rewrite (is_heap heap s) as (is_heap heap (PI.pool_init 'g (U64.v i) (U64.v c)))
  } else {
    with s. assert (is_heap heap s);
    rewrite (is_heap heap s) as (is_heap heap (PI.pool_init 'g (U64.v i) (U64.v c)))
  }
}

/// ---------------------------------------------------------------------------
/// Taking a free page
/// ---------------------------------------------------------------------------

let acq_rec (i: U64.t{U64.v i < n_pages}) (c: U64.t{U64.v c < n_cls}) (nx: U64.t) : pinfo =
  PI.slot_fits (U64.v i) (U64.v c) 0;
  { code = 1uy; arg = c; swept = true;
    free_head = U64.add (slot_base_u64 i c 0UL) 8UL;
    nfree = n_slots_u64 c; next = nx }

let acq_rec_view (st: pstate) (i: U64.t{U64.v i < n_pages}) (c: U64.t{U64.v c < n_cls})
  : Lemma (requires Seq.length st.avail == n_cls)
          (ensures view (acq_rec i c (Seq.index st.avail (U64.v c))) ==
                   P.acq_entry st (U64.v i) (U64.v c))
  = PI.slot_fits (U64.v i) (U64.v c) 0

let acq_state_eq (st: pstate) (i: U64.t{U64.v i < n_pages}) (c: U64.t{U64.v c < n_cls})
  : Lemma (requires Seq.length st.avail == n_cls)
          (ensures set_avail_at (set_entry st (U64.v i) (view (acq_rec i c (Seq.index st.avail (U64.v c)))))
                                (U64.v c) (U64.add i 1UL) ==
                   P.acq_state st (U64.v i) (U64.v c))
  = acq_rec_view st i c;
    n_pages_small ();
    FStar.Math.Lemmas.pow2_lt_compat 64 54

fn acquire (heap: heap_t) (t: pstate_t) (i: U64.t{U64.v i < n_pages}) (c: U64.t{U64.v c < n_cls})
  (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st
  ensures is_heap heap (fst (P.acquire 'g st (U64.v i) (U64.v c))) **
          pages_st t (snd (P.acquire 'g st (U64.v i) (U64.v c)))
{
  let cl = cls_at t c;
  let ns = ns_at t c;
  pool_init heap i c cl ns;
  let nx = read_avail t c;
  n_pages_small ();
  FStar.Math.Lemmas.pow2_lt_compat 64 54;
  write_used t i (acq_rec i c nx);
  write_avail t c (U64.add i 1UL);
  acq_state_eq st i c;
  with st'. assert (pages_st t st');
  rewrite (pages_st t st') as (pages_st t (snd (P.acquire 'g st (U64.v i) (U64.v c))));
  rewrite (is_heap heap (PI.pool_init 'g (U64.v i) (U64.v c)))
       as (is_heap heap (fst (P.acquire 'g st (U64.v i) (U64.v c))))
}

/// ---------------------------------------------------------------------------
/// Taking a slot
/// ---------------------------------------------------------------------------

/// `fill_slot_as false`, unfolded: the filler, then the header.
let fill_unfold_f (g: Base.heap) (p: nat) (c: nat{c < n_cls}) (k: nat) (wz: nat{P.small_wz wz c})
                  (a x: nat) (vb vo: U64.t)
  : Lemma (requires a == slot_base p c k /\ x == a + (wz + 1) * 8 /\ wz + 1 < cls c /\
                    vb == B.bhdr (cls c - (wz + 1)) /\ vo == B.ohdr wz)
          (ensures P.fill_slot_as false g p c k wz == B.wr (B.wr g x vb) a vo)
  = cls_bounds c

let fill_unfold_n (g: Base.heap) (p: nat) (c: nat{c < n_cls}) (k: nat) (wz: nat{P.small_wz wz c})
                  (a: nat) (vo: U64.t)
  : Lemma (requires a == slot_base p c k /\ ~(wz + 1 < cls c) /\ vo == B.ohdr wz)
          (ensures P.fill_slot_as false g p c k wz == B.wr g a vo)
  = cls_bounds c

let fill_bound (p: nat{p < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c}) (wz: nat{P.small_wz wz c})
  : Lemma (slot_base p c k + (wz + 1) * 8 < pow2 64)
  = PI.slot_fits p c k;
    cls_bounds c;
    FStar.Math.Lemmas.pow2_lt_compat 64 57;
    assert_norm (pow2 57 + pow2 20 * 8 < pow2 64)

/// The state after a pop, as the specification builds it.
let pop_state (st: pstate) (p: nat{p < n_pages /\ (entry st.pm p).nfree > 0}) (c: nat{c < n_cls}) (nx: U64.t) : pstate =
  let e = entry st.pm p in
  let e' = { e with free_head = nx; nfree = e.nfree - 1 } in
  { st with pm = Seq.upd st.pm p e';
            avail = (if e.nfree = 1 then P.set_avail st c e.next else st.avail) }

let pop_unfold (g: Base.heap) (st: pstate) (c: nat{c < n_cls}) (wz: nat{P.small_wz wz c})
                (p: nat{p < n_pages}) (k: nat)
  : Lemma (requires P.avail_at st c <> 0UL /\ U64.v (P.avail_at st c) == p + 1 /\
                    k == P.slot_of p c (entry st.pm p).free_head /\
                    k < n_slots c /\ (entry st.pm p).nfree > 0)
          (ensures (PI.slot_fits p c k;
                    P.pop_as false g st c wz ==
                    (P.fill_slot_as false g p c k wz,
                     pop_state st p c (Sh.hdr g (slot_obj p c k)),
                     U64.uint_to_t (slot_obj p c k))))
  = ()

let pop_state_eq (st: pstate) (p: U64.t{U64.v p < n_pages}) (c: U64.t{U64.v c < n_cls}) (nx nf: U64.t)
  : Lemma (requires U64.v nf == (entry st.pm (U64.v p)).nfree /\ U64.v nf > 0 /\ Seq.length st.avail == n_cls)
          (ensures (let st1 = set_slots st (U64.v p) nx (U64.sub nf 1UL) in
                    (if U64.v nf = 1 then set_avail_at st1 (U64.v c) (entry st.pm (U64.v p)).next else st1) ==
                    pop_state st (U64.v p) (U64.v c) nx))
  = ()

/// The list entry of slot `k` names slot `k`.
let slot_of_obj (p: nat{p < n_pages}) (c: nat{c < n_cls}) (k: nat) (s: U64.t)
  : Lemma (requires U64.v s == slot_obj p c k) (ensures P.slot_of p c s == k)
  = cls_bounds c;
    FStar.Math.Lemmas.paren_mul_right k (cls c) 8;
    FStar.Math.Lemmas.cancel_mul_div k (cls c * 8)

/// What the fast path reads from a ready head.
let ready_head (st: pstate) (c: nat{c < n_cls})
  : Lemma (requires Rd.head_ready st c /\ Seq.index st.avail c <> 0UL)
          (ensures (let p = U64.v (Seq.index st.avail c) - 1 in
                    p < n_pages /\
                    (let e = entry st.pm p in
                     let k = P.slot_of p c e.free_head in
                     e.kind == Pool c /\ e.nfree > 0 /\ k < n_slots c /\
                     U64.v e.free_head == slot_obj p c k)))
  = let p = U64.v (Seq.index st.avail c) - 1 in
    let e = entry st.pm p in
    eliminate exists (k: nat). k < n_slots c /\ U64.v e.free_head == slot_obj p c k
    with slot_of_obj p c k e.free_head

/// The filler of a slot lies in the heap.
let filler_in_heap (p: nat{p < n_pages}) (c: nat{c < n_cls}) (k: nat{k < n_slots c}) (w: nat)
  : Lemma (requires w < cls c)
          (ensures (slot_base p c k + w * 8) % 8 == 0 /\ slot_base p c k + w * 8 + 8 <= Base.heap_size)
  = PI.slot_fits p c k;
    slot_base_succ p c k;
    slot_base_aligned p c k;
    FStar.Math.Lemmas.lemma_mult_le_right (cls c * 8) (k + 1) (n_slots c);
    FStar.Math.Lemmas.paren_mul_right (k + 1) (cls c) 8

/// Slot `k`, at `a`, takes the object: a filler, then the header
/// (`Pool.fill_slot_as false`).
fn fill_at (heap: heap_t) (a: U64.t) (c: U64.t{U64.v c < n_cls}) (cl: U64.t{U64.v cl == cls (U64.v c)})
  (wz: U64.t{P.small_wz (U64.v wz) (U64.v c)}) (#p: erased nat{p < n_pages}) (#k: erased nat)
  requires is_heap heap 'g ** pure (k < n_slots (U64.v c) /\ U64.v a == slot_base p (U64.v c) k)
  ensures exists* g'. is_heap heap g' ** pure (g' == P.fill_slot_as false 'g p (U64.v c) k (U64.v wz))
{
  cls_bounds (U64.v c);
  FStar.Math.Lemmas.pow2_lt_compat 54 20;
  PI.slot_fits p (U64.v c) k;
  fill_bound p (U64.v c) k (U64.v wz);
  let w = U64.add wz 1UL;
  let vo = ohdr_u64 wz;
  if (U64.lt w cl) {
    let x = U64.add a (U64.mul w 8UL);
    let vb = bhdr_u64 (U64.sub cl w);
    filler_in_heap p (U64.v c) k (U64.v w);
    write_word heap x vb;
    write_word heap a vo;
    fill_unfold_f 'g p (U64.v c) k (U64.v wz) (U64.v a) (U64.v x) vb vo;
  } else {
    write_word heap a vo;
    fill_unfold_n 'g p (U64.v c) k (U64.v wz) (U64.v a) vo;
  }
}

fn pop (heap: heap_t) (t: pstate_t) (c: U64.t{U64.v c < n_cls}) (wz: U64.t{P.small_wz (U64.v wz) (U64.v c)})
  (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st **
           pure (Rd.head_ready st (U64.v c) /\ Seq.index st.avail (U64.v c) <> 0UL)
  returns o: U64.t
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure ((g', st', o) == P.pop_as false 'g st (U64.v c) (U64.v wz))
{
  pages_st_lengths t;
  let hd = read_avail t c;
  ready_head st (U64.v c);
  let p = U64.sub hd 1UL;
  let sl = read_slots t p;
  let so = sl.pfree_head;
  let nf = sl.pnfree;
  let k : erased nat = hide (P.slot_of (U64.v p) (U64.v c) so);
  PI.slot_fits (U64.v p) (U64.v c) k;
  let nx = read_word heap so;
  pop_unfold 'g st (U64.v c) (U64.v wz) (U64.v p) k;
  pop_state_eq st p c nx nf;
  write_slots t p nx (U64.sub nf 1UL);
  let cl = cls_at t c;
  if (nf = 1UL) {
    write_avail t c sl.pnext;
    fill_at heap (U64.sub so 8UL) c cl wz #(U64.v p) #k;
    so
  } else {
    fill_at heap (U64.sub so 8UL) c cl wz #(U64.v p) #k;
    so
  }
}

/// ---------------------------------------------------------------------------
/// Small allocation
/// ---------------------------------------------------------------------------

let small_unfold (g: Base.heap) (st: pstate) (wz: nat{wz + 1 <= small_max})
  : Lemma (let c = class_of (wz + 1) in
           class_of_fits (wz + 1);
           P.small_wz_intro wz c;
           P.small_alloc_as false g st wz ==
           (if P.avail_at st c <> 0UL then P.pop_as false g st c wz
            else begin
              let i = P.find_free st.pm 0 in
              if i >= n_pages then (g, st, 0UL)
              else begin
                let (g1, st1) = P.acquire g st i c in
                P.pop_as false g1 st1 c wz
              end
            end))
  = ()

/// A page just taken heads its class's list, ready.
let acquire_ready (st: pstate) (i: nat{i < n_pages}) (c: nat{c < n_cls})
  : Lemma (requires Seq.length st.avail == n_cls)
          (ensures Rd.head_ready (P.acq_state st i c) c /\
                   Seq.index (P.acq_state st i c).avail c <> 0UL)
  = n_pages_small ();
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    PI.slot_fits i c 0;
    assert (U64.v (PI.pool_entry i c).free_head == slot_obj i c 0)

fn small_alloc (heap: heap_t) (t: pstate_t) (wz: U64.t{U64.v wz + 1 <= small_max})
  (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st ** pure (Rd.heads_ready st)
  returns o: U64.t
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure ((g', st', o) == P.small_alloc_as false 'g st (U64.v wz))
{
  pages_st_lengths t;
  cls_bounds (n_cls - 1);
  FStar.Math.Lemmas.pow2_lt_compat 64 20;
  let c = class_at t (U64.add wz 1UL);
  class_of_fits (U64.v wz + 1);
  P.small_wz_intro (U64.v wz) (U64.v c);
  small_unfold 'g st (U64.v wz);
  let hd = read_avail t c;
  if (hd <> 0UL) {
    pop heap t c wz
  } else {
    let i = find_free t;
    let np = n_pages_u64 ();
    if (U64.gte i np) {
      0UL
    } else {
      acquire_ready st (U64.v i) (U64.v c);
      acquire heap t i c;
      pop heap t c wz
    }
  }
}
