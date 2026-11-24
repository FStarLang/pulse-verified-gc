/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.AllocTagged - the allocation paths with the header given
/// ---------------------------------------------------------------------------
///
/// Plan §27.8.  The page allocator's paths (`GC.Impl.Pages.Pool.fill_at`,
/// `pop`, `small_alloc`; `GC.Impl.Pages.Large.carve_at`, `carve`, `new_run`,
/// `large_alloc`) with the new object's header a parameter `vh`, written in
/// place of `ohdr wz`.  In every path that header is the last word written
/// to the heap, so the result is the specification's with that one word
/// rewritten (`GC.Spec.Pages.AllocTag.rehdr`).  The tagged allocator
/// (`GC.Impl.Pages.Alloc.alloc_tag`) passes the header with its colour and
/// tag, so it writes the header once, as the untagged allocator does,
/// instead of writing `ohdr wz` and then the tagged header.
///
/// The functions of `Pool` and `Large`, and their C, are unchanged; their
/// lemmas are reused.

module GC.Impl.Pages.AllocTagged

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

module U64 = FStar.UInt64
module L = FStar.List.Tot
module Base = GC.Spec.Base
module SO = GC.Spec.Object
module Sh = GC.Spec.Pages.Shape
module B = GC.Spec.Pages.Blocks
module PI = GC.Spec.Pages.PoolInit
module P = GC.Spec.Pages.Pool
module Ce = GC.Spec.Pages.Cells
module LG = GC.Spec.Pages.Large
module NR = GC.Spec.Pages.NewRun
module T = GC.Spec.Pages.Theorems
module A = GC.Spec.Pages.Alloc
module AT = GC.Spec.Pages.AllocTag
module Rd = GC.Impl.Pages.Ready
module PL = GC.Impl.Pages.Pool
module LI = GC.Impl.Pages.Large

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

/// A guarded write at a word of the heap is the write.
let wr_eq (g: Base.heap) (a: Base.hp_addr) (v: U64.t)
  : Lemma (B.wr g (U64.v a) v == GC.Spec.Heap.write_word g a v)
  = ()

/// ---------------------------------------------------------------------------
/// Small blocks
/// ---------------------------------------------------------------------------

/// `PL.fill_at`, the header `vh`.
fn fill_at_h (heap: heap_t) (a: U64.t) (c: U64.t{U64.v c < n_cls}) (cl: U64.t{U64.v cl == cls (U64.v c)})
  (wz: U64.t{P.small_wz (U64.v wz) (U64.v c)}) (vh: U64.t) (#p: erased nat{p < n_pages}) (#k: erased nat)
  requires is_heap heap 'g ** pure (k < n_slots (U64.v c) /\ U64.v a == slot_base p (U64.v c) k)
  ensures exists* g'. is_heap heap g' **
          pure (g' == B.wr (P.fill_slot_as false 'g p (U64.v c) k (U64.v wz)) (U64.v a) vh)
{
  cls_bounds (U64.v c);
  FStar.Math.Lemmas.pow2_lt_compat 54 20;
  PI.slot_fits p (U64.v c) k;
  PL.fill_bound p (U64.v c) k (U64.v wz);
  let w = U64.add wz 1UL;
  if (U64.lt w cl) {
    let x = U64.add a (U64.mul w 8UL);
    let vb = bhdr_u64 (U64.sub cl w);
    PL.filler_in_heap p (U64.v c) k (U64.v w);
    write_word heap x vb;
    write_word heap a vh;
    wr_eq 'g x vb;
    wr_eq (GC.Spec.Heap.write_word 'g x vb) a vh;
    PL.fill_unfold_f 'g p (U64.v c) k (U64.v wz) (U64.v a) (U64.v x) vb (B.ohdr (U64.v wz));
    AT.wr_wr (B.wr 'g (U64.v x) vb) (U64.v a) (B.ohdr (U64.v wz)) vh;
    assert (pure (GC.Spec.Heap.write_word (GC.Spec.Heap.write_word 'g x vb) a vh == B.wr (B.wr 'g (U64.v x) vb) (U64.v a) vh));
    assert (pure (P.fill_slot_as false 'g p (U64.v c) k (U64.v wz) == B.wr (B.wr 'g (U64.v x) vb) (U64.v a) (B.ohdr (U64.v wz))));
  } else {
    write_word heap a vh;
    wr_eq 'g a vh;
    PL.fill_unfold_n 'g p (U64.v c) k (U64.v wz) (U64.v a) (B.ohdr (U64.v wz));
    AT.wr_wr 'g (U64.v a) (B.ohdr (U64.v wz)) vh;
    assert (pure (GC.Spec.Heap.write_word 'g a vh == B.wr 'g (U64.v a) vh));
    assert (pure (P.fill_slot_as false 'g p (U64.v c) k (U64.v wz) == B.wr 'g (U64.v a) (B.ohdr (U64.v wz))));
  }
}

/// `PL.pop`, the header `vh`.
fn pop_h (heap: heap_t) (t: pstate_t) (c: U64.t{U64.v c < n_cls}) (wz: U64.t{P.small_wz (U64.v wz) (U64.v c)})
  (vh: U64.t) (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st **
           pure (Rd.head_ready st (U64.v c) /\ Seq.index st.avail (U64.v c) <> 0UL)
  returns o: U64.t
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure ((g', st', o) == AT.rehdr (P.pop_as false 'g st (U64.v c) (U64.v wz)) vh)
{
  pages_st_lengths t;
  let hd = read_avail t c;
  PL.ready_head st (U64.v c);
  let p = U64.sub hd 1UL;
  let sl = read_slots t p;
  let so = sl.pfree_head;
  let nf = sl.pnfree;
  let k : erased nat = hide (P.slot_of (U64.v p) (U64.v c) so);
  PI.slot_fits (U64.v p) (U64.v c) k;
  let nx = read_word heap so;
  PL.pop_unfold 'g st (U64.v c) (U64.v wz) (U64.v p) k;
  PL.pop_state_eq st p c nx nf;
  write_slots t p nx (U64.sub nf 1UL);
  let cl = cls_at t c;
  if (nf = 1UL) {
    write_avail t c sl.pnext;
    PL.tail_if t (sl.pnext = 0UL) c 0UL;
    fill_at_h heap (U64.sub so 8UL) c cl wz vh #(U64.v p) #k;
    so
  } else {
    fill_at_h heap (U64.sub so 8UL) c cl wz vh #(U64.v p) #k;
    so
  }
}

/// `PL.small_alloc`, the header `vh`.
fn small_alloc_h (heap: heap_t) (t: pstate_t) (wz: U64.t{U64.v wz + 1 <= small_max}) (vh: U64.t)
  (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st ** pure (Rd.heads_ready st)
  returns o: U64.t
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure ((g', st', o) == AT.rehdr (P.small_alloc_as false 'g st (U64.v wz)) vh)
{
  pages_st_lengths t;
  cls_bounds (n_cls - 1);
  FStar.Math.Lemmas.pow2_lt_compat 64 20;
  let c = class_at t (U64.add wz 1UL);
  class_of_fits (U64.v wz + 1);
  P.small_wz_intro (U64.v wz) (U64.v c);
  PL.small_unfold 'g st (U64.v wz);
  let hd = read_avail t c;
  if (hd <> 0UL) {
    pop_h heap t c wz vh
  } else {
    let i = PL.find_free t;
    let np = n_pages_u64 ();
    if (U64.gte i np) {
      0UL
    } else {
      PL.acquire_ready st (U64.v i) (U64.v c);
      PL.acquire heap t i c;
      pop_h heap t c wz vh
    }
  }
}

/// ---------------------------------------------------------------------------
/// Large blocks
/// ---------------------------------------------------------------------------

/// `LI.carve_at`, the header `vh`.
fn carve_at_h (heap: heap_t) (c: U64.t{Ce.node c}) (wz: U64.t{U64.v wz < pow2 54}) (vh: U64.t)
  requires is_heap heap 'g
  returns o: U64.t
  ensures exists* g'. is_heap heap g' **
          pure (U64.v o >= 8 /\ o == LG.obj_of 'g c (U64.v wz) /\
                g' == B.wr (LG.carved_as false 'g c (U64.v wz)) (U64.v o - 8) vh)
{
  LI.bounds ();
  let ws = LI.whsize_at heap c;
  let w = U64.add wz 1UL;
  let l = (if U64.gte ws w then U64.sub ws w else 0UL);
  let h = U64.sub c 8UL;
  FStar.Math.Lemmas.pow2_lt_compat 64 57;
  FStar.Math.Lemmas.pow2_plus 54 3;
  let x = U64.add h (U64.mul l 8UL);
  FStar.UInt.shift_left_value_lemma #64 1 54;
  if (U64.gte l 1UL && U64.lte l (U64.shift_left 1UL 54ul)) {
    wr heap h (bhdr_u64 l);
    wr heap x vh;
    LI.carved_split 'g c (U64.v wz) (U64.v h) (U64.v l) (U64.v x);
    AT.wr_wr (B.wr 'g (U64.v h) (B.bhdr (U64.v l))) (U64.v x) (B.ohdr (U64.v wz)) vh;
    U64.add x 8UL
  } else {
    wr heap h vh;
    LI.carved_whole 'g c (U64.v wz) (U64.v h);
    AT.wr_wr 'g (U64.v h) (B.ohdr (U64.v wz)) vh;
    U64.add x 8UL
  }
}

/// `LI.carve`, the header `vh`.
fn carve_h (heap: heap_t) (t: pstate_t) (c: U64.t{Ce.node c}) (prev: U64.t) (wz: U64.t{U64.v wz < pow2 54})
  (vh: U64.t) (#st: erased pstate) (pre: erased (list Base.obj_addr))
  requires is_heap heap 'g ** pages_st t st **
           pure ((reveal pre == [] ==> prev == 0UL) /\
                 (reveal pre =!= [] ==> prev == (L.last pre <: U64.t) /\ prev <> 0UL))
  returns o: U64.t
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure ((g', st', o) == AT.rehdr (LG.carve_as false 'g st pre c (U64.v wz)) vh)
{
  LI.bounds ();
  LI.carve_unfold 'g st pre c (U64.v wz);
  let ws = LI.whsize_at heap c;
  let w = U64.add wz 1UL;
  if (U64.lt ws w) {
    0UL
  } else {
    if (U64.gte (U64.sub ws w) (LI.lg_min_u64 ())) {
      carve_at_h heap c wz vh
    } else {
      let nx = read_word heap c;
      if (prev = 0UL) {
        LI.unlink_nil 'g st nx;
        write_lhead t nx;
        carve_at_h heap c wz vh
      } else {
        LI.unlink_cons 'g st pre nx;
        wr heap prev nx;
        carve_at_h heap c wz vh
      }
    }
  }
}

/// `LI.new_run`, the header `vh`.
fn new_run_h (heap: heap_t) (t: pstate_t) (i: U64.t) (k: U64.t{U64.v k > 0 /\ U64.v i + U64.v k <= n_pages})
  (wz: U64.t{U64.v wz + 1 <= U64.v k * page_wsize /\ U64.v wz < pow2 54}) (vh: U64.t)
  (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st
  returns o: U64.t
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure ((g', st', o) == AT.rehdr (NR.new_run_as false 'g st (U64.v i) (U64.v k) (U64.v wz)) vh)
{
  LI.bounds ();
  let w = U64.add wz 1UL;
  LI.run_bound (U64.v i) (U64.v k) (U64.v w);
  let a = page_base_u64 i;
  let r = U64.sub (U64.mul k page_wsize_u64) w;
  let hd0 = read_lhead t;
  let x = U64.add a (U64.mul w 8UL);
  let o = U64.add x 8UL;
  let ob = U64.add a 8UL;
  FStar.UInt.shift_left_value_lemma #64 1 54;
  if (U64.gt r 0UL && U64.lte r (U64.shift_left 1UL 54ul)) {
    if (U64.gte r (LI.lg_min_u64 ())) {
      LI.run_listed 'g st (U64.v i) (U64.v k) (U64.v wz) hd0 (U64.v a) (U64.v x) (U64.v r) o;
      wr heap x (bhdr_u64 r);
      wr heap o hd0;
      wr heap a vh;
      AT.wr_wr (B.wr (B.wr 'g (U64.v x) (B.bhdr (U64.v r))) (U64.v o) hd0) (U64.v a) (B.ohdr (U64.v wz)) vh;
      LI.write_run t i k;
      write_lhead t o;
      ob
    } else {
      LI.run_unlisted 'g st (U64.v i) (U64.v k) (U64.v wz) hd0 (U64.v a) (U64.v x) (U64.v r);
      wr heap x (bhdr_u64 r);
      wr heap a vh;
      AT.wr_wr (B.wr 'g (U64.v x) (B.bhdr (U64.v r))) (U64.v a) (B.ohdr (U64.v wz)) vh;
      LI.write_run t i k;
      ob
    }
  } else {
    LI.run_full 'g st (U64.v i) (U64.v k) (U64.v wz) hd0 (U64.v a) (U64.v r);
    wr heap a vh;
    AT.wr_wr 'g (U64.v a) (B.ohdr (U64.v wz)) vh;
    LI.write_run t i k;
    ob
  }
}

/// `LI.large_alloc`, the header `vh`.
fn large_alloc_h (heap: heap_t) (t: pstate_t) (wz: U64.t{U64.v wz < pow2 54}) (vh: U64.t)
  (#st: erased pstate)
  requires is_heap heap 'g ** pages_st t st
  returns o: U64.t
  ensures exists* g' st'. is_heap heap g' ** pages_st t st' **
          pure ((g', st', o) == AT.rehdr (A.large_alloc_as false 'g st (U64.v wz)) vh)
{
  LI.bounds ();
  LI.large_unfold 'g st (U64.v wz);
  let w = U64.add wz 1UL;
  let fp = read_lhead t;
  let res = LI.find_fit heap fp w;
  let found = (match res with | (f, _, _) -> f);
  let prev = (match res with | (_, p, _) -> p);
  let c = (match res with | (_, _, c) -> c);
  if found {
    LI.fit_pre 'g fp (U64.v w) prev c;
    let pre = LI.fit_pre_list 'g fp (U64.v w) prev c;
    carve_h heap t c prev wz vh pre
  } else {
    FStar.Math.Lemmas.pow2_lt_compat 64 54;
    let k = LI.pages_for_u64 w;
    LI.pages_for_ok (U64.v w);
    let i = LI.find_run t k;
    LI.find_run_le st.pm (U64.v k) 0;
    let np = n_pages_u64 ();
    if (U64.gt k (U64.sub np i)) {
      0UL
    } else {
      new_run_h heap t i k wz vh
    }
  }
}
