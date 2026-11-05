(*
   Pulse GC - Allocator Implementation

   Size-segregated free-list allocator verified against
   GC.Spec.Allocator.Lists.  Tries the list of the request's own size, then
   the larger small lists, then list 0, skipping empty heads; on each, first
   fit without writing (`find_fit`), then the writes: the single-list split,
   or, when the remainder's size class changes, the remainder moved to its
   own list.  Fully proved — 0 admits.
*)

module GC.Impl.Allocator

#lang-pulse

#set-options "--fuel 1 --ifuel 0 --z3rlimit 12"

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module R = Pulse.Lib.Reference
module SpecBase = GC.Spec.Base
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SA = GC.Spec.Allocator
module SF = GC.Spec.Fields
module SO = GC.Spec.Object
module SH = GC.Spec.Heap
module SI = GC.Spec.SweepInv
module AllocLemmas = GC.Spec.Allocator.Lemmas
module SpecAlloc = GC.Spec.Allocator
module SpecFields = GC.Spec.Fields
module SpecObject = GC.Spec.Object
module SAL = GC.Spec.Allocator.Lists
module FLs = GC.Spec.FreeLists
module SC = GC.Spec.SizeClass

/// ---------------------------------------------------------------------------
/// Pure helper lemmas (all proven — no admits)
/// ---------------------------------------------------------------------------

/// init_heap postcondition when heap is too small
let init_heap_small_lemma (s: heap_state)
  : Lemma (requires SpecBase.heap_words < 2)
          (ensures (s, 0UL) == SA.init_heap_spec s)
  = ()

/// init_heap postcondition for the normal case
let init_heap_normal_lemma (s: heap_state) (hdr: U64.t)
                           (wz: wosize{U64.v wz == SpecBase.heap_words - 1})
  : Lemma (requires SpecBase.heap_words >= 2 /\
                    hdr == makeHeader wz blue 0UL)
          (ensures ((SH.write_word (SH.write_word s zero_addr hdr)
                                          (mword <: hp_addr) 0UL, mword)
                    <: SpecBase.heap & U64.t)
                   == SA.init_heap_spec s)
  = ()

/// Fuel bound for search loop
let fuel_bound_lemma (fuel: U64.t)
  : Lemma (requires U64.v fuel > 0 /\ U64.v fuel <= heap_size / 8)
          (ensures U64.v (U64.sub fuel 1UL) <= heap_size / 8)
  = ()

/// `fuel <> 0UL ==> U64.v fuel > 0`.
///
/// Trivial, but every proof obligation is now discharged as its own SMT query
/// carrying the enclosing Pulse loop's full context, in which even this times
/// out.  Proving it here, where the context is empty, removes the SMT call at
/// the use site.
let fuel_nonzero_lemma (fuel: U64.t)
  : Lemma (requires fuel <> 0UL) (ensures U64.v fuel > 0)
  = ()

/// wosize bound: any wz that fits in a valid block is within pow2 54 - 1
let wosize_bound_lemma (wz: U64.t) (block_wz: U64.t)
  : Lemma (requires U64.v block_wz >= U64.v wz /\ U64.v block_wz <= pow2 54 - 1)
          (ensures U64.v wz <= pow2 54 - 1)
  = ()

/// Arithmetic for split: (wz + 1) * 8 fits in 64 bits when wz <= pow2 54 - 1
let split_offset_fits (wz: U64.t)
  : Lemma (requires U64.v wz <= pow2 54 - 1)
          (ensures U64.v wz + 1 <= pow2 54 /\
                   (U64.v wz + 1) * U64.v mword <= pow2 57 /\
                   (U64.v wz + 1) * U64.v mword < pow2 64)
  = assert_norm (pow2 54 * 8 == pow2 57);
    assert_norm (pow2 57 < pow2 64)

/// No-overflow for split address computations
let split_no_overflow (hd: hp_addr) (wz: U64.t)
  : Lemma (requires U64.v wz <= pow2 54 - 1)
          (ensures (let offset = (U64.v wz + 1) * 8 in
                    U64.v hd + offset < pow2 64 /\
                    U64.v hd + offset + 8 < pow2 64))
  = split_offset_fits wz;
    assert_norm (pow2 57 + pow2 57 == pow2 58);
    assert_norm (pow2 58 < pow2 64)

/// Arithmetic for right-justified allocation: the object header sits at
/// `hd + leftover * 8`.  Establishes that it is word-aligned and that neither
/// it nor the object address one word above it overflows 64 bits.
let rightjust_no_overflow (hd: hp_addr) (leftover: U64.t)
  : Lemma (requires U64.v leftover <= pow2 54 - 1)
          (ensures (let off = U64.v leftover * U64.v mword in
                    off <= pow2 57 /\
                    off < pow2 64 /\
                    U64.v hd + off < pow2 64 /\
                    U64.v hd + off + U64.v mword < pow2 64 /\
                    (U64.v hd + off) % U64.v mword == 0))
  = assert_norm (pow2 54 * 8 == pow2 57);
    assert_norm (pow2 57 + pow2 57 == pow2 58);
    assert_norm (pow2 58 + pow2 58 == pow2 59);
    assert_norm (pow2 59 < pow2 64);
    FStar.Math.Lemmas.multiple_modulo_lemma (U64.v leftover) 8;
    FStar.Math.Lemmas.lemma_mod_add_distr (U64.v hd) (U64.v leftover * 8) 8

/// wosize bounds from heap arithmetic
let wosize_from_heap_lemma (wz: U64.t)
  : Lemma (requires U64.v wz <= SpecBase.heap_words - 1 /\ heap_size <= pow2 57)
          (ensures U64.v wz <= pow2 54 - 1)
  = assert_norm (pow2 57 / 8 == pow2 54);
    FStar.Math.Lemmas.lemma_div_le heap_size (pow2 57) 8

/// Connect impl's hd_address with spec's (both are obj - mword)
let hd_address_eq (obj: obj_addr)
  : Lemma (hd_address obj == SH.hd_address obj)
  = SH.hd_address_spec obj

/// ---------------------------------------------------------------------------
/// Helper: check if a U64 is a valid obj_addr for free-list traversal
/// ---------------------------------------------------------------------------

let is_valid_fp (v: U64.t) : bool =
  U64.gte v (U64.add zero_addr mword) &&
  U64.lt v heap_size_u64 &&
  (U64.rem v mword = 0UL)

/// ---------------------------------------------------------------------------
/// Heap initialization (fully proved)
/// ---------------------------------------------------------------------------

fn init_heap_single (heap: heap_t)
  requires is_heap heap 's
  returns fp: U64.t
  ensures exists* s2. is_heap heap s2 **
    pure ((s2, fp) == SA.init_heap_spec 's)
{
  let total_words = U64.div heap_size_u64 mword;
  if U64.lt total_words 2UL {
    init_heap_small_lemma 's;
    0UL
  } else {
    let wz = U64.sub total_words 1UL;
    assert_norm (pow2 57 / 8 == pow2 54);
    FStar.Math.Lemmas.lemma_div_le heap_size (pow2 57) 8;
    assert (pure (U64.v wz >= 1));
    let hdr = makeHeader wz blue 0UL;
    write_word heap zero_addr hdr;

    assert (pure (U64.v mword < heap_size));
    write_word heap mword 0UL;

    init_heap_normal_lemma 's hdr wz;
    mword
  }
}

/// Two distinct word-aligned addresses are a full word apart, so writing at
/// one leaves the other's word intact.  Used to show that repairing the
/// predecessor's link does not disturb the block header the allocation then
/// reads back.
let prev_write_keeps_header (g: SpecBase.heap) (p: SpecBase.hp_addr)
                            (hd: SpecBase.hp_addr) (v: U64.t)
  : Lemma (requires U64.v p <> U64.v hd)
          (ensures SH.read_word (SH.write_word g p v) hd == SH.read_word g hd)
  = SH.read_write_different g p hd v

/// ---------------------------------------------------------------------------
/// First fit on one list
/// ---------------------------------------------------------------------------

/// First fit on the list headed by `fp`, without writing anything: the block
/// it stops at and that block's predecessor (`GC.Spec.Allocator.Lists.
/// first_fit_block` and `found_prev`), or a block of 0 when nothing fits.
#push-options "--z3rlimit 60"
inline_for_extraction
fn find_fit (heap: heap_t) (fp: U64.t) (wz: U64.t)
  requires is_heap heap 's ** pure (U64.v wz >= 1)
  returns res: (U64.t & U64.t)
  ensures is_heap heap 's **
    pure (let p = fst res in
          let c = snd res in
          (c == 0UL <==> (SA.alloc_spec 's fp (U64.v wz)).SA.obj_out == 0UL) /\
          (c <> 0UL ==>
             c == SAL.first_fit_block 's fp (U64.v wz) SpecBase.heap_words /\
             p == SAL.found_prev 's 0UL fp (U64.v wz) SpecBase.heap_words /\
             (p == 0UL \/
              (U64.v p >= U64.v mword /\ U64.v p < heap_size /\ U64.v p % U64.v mword == 0))))
{
  let mut prev_fp = 0UL;
  let mut cur_fp = fp;
  let mut res_p = 0UL;
  let mut res_c = 0UL;
  let mut go = true;
  let mut fuel_ref : U64.t = U64.div heap_size_u64 mword;

  while (!go)
    invariant exists* vgo vfuel vprev vcur vp vc.
      R.pts_to go vgo **
      R.pts_to fuel_ref vfuel **
      R.pts_to prev_fp vprev **
      R.pts_to cur_fp vcur **
      R.pts_to res_p vp **
      R.pts_to res_c vc **
      is_heap heap 's **
      pure (
        U64.v vfuel <= heap_size / 8 /\
        (vprev == 0UL \/
         (U64.v vprev >= U64.v mword /\ U64.v vprev < heap_size /\
          U64.v vprev % U64.v mword == 0)) /\
        (if vgo then
          vc == 0UL /\
          SA.alloc_search 's fp vprev vcur (U64.v wz) (U64.v vfuel) ==
            SA.alloc_spec 's fp (U64.v wz) /\
          SAL.first_fit_block 's vcur (U64.v wz) (U64.v vfuel) ==
            SAL.first_fit_block 's fp (U64.v wz) SpecBase.heap_words /\
          SAL.found_prev 's vprev vcur (U64.v wz) (U64.v vfuel) ==
            SAL.found_prev 's 0UL fp (U64.v wz) SpecBase.heap_words
        else
          (vc == 0UL <==> (SA.alloc_spec 's fp (U64.v wz)).SA.obj_out == 0UL) /\
          (vc <> 0UL ==>
             vc == SAL.first_fit_block 's fp (U64.v wz) SpecBase.heap_words /\
             vp == SAL.found_prev 's 0UL fp (U64.v wz) SpecBase.heap_words /\
             (vp == 0UL \/
              (U64.v vp >= U64.v mword /\ U64.v vp < heap_size /\ U64.v vp % U64.v mword == 0))))
      )
    decreases (U64.v !fuel_ref + (if !go then 1 else 0))
  {
    let vfuel = !fuel_ref;
    if U64.eq vfuel 0UL {
      let vp = !prev_fp;
      let vc = !cur_fp;
      SA.alloc_search_fuel_0 's fp vp vc (U64.v wz);
      go := false
    } else {
      fuel_nonzero_lemma vfuel;
      let vcur = !cur_fp;
      let valid = is_valid_fp vcur;
      if not valid {
        let vp = !prev_fp;
        SA.alloc_search_invalid 's fp vp vcur (U64.v wz) (U64.v vfuel);
        go := false
      } else {
        hd_address_eq vcur;
        let hd_addr = hd_address vcur;
        let hdr = read_word heap hd_addr;
        let block_wz = getWosize hdr;
        getWosize_eq hdr;
        let next = read_word heap vcur;
        SA.spec_next_fp_eq 's (vcur <: obj_addr);
        if U64.gte block_wz wz {
          let leftover = U64.sub block_wz wz;
          let vp = !prev_fp;
          wosize_bound_lemma wz block_wz;
          rightjust_no_overflow hd_addr leftover;
          let alloc_hd_off = U64.add hd_addr (U64.mul leftover mword);
          let alloc_obj = U64.add alloc_hd_off mword;
          if U64.gte alloc_obj heap_size_u64 {
            // the right-justified object would leave the heap
            SA.alloc_search_found_oob 's fp vp vcur (U64.v wz) (U64.v vfuel);
            go := false
          } else {
            // found: the search allocates here
            (if (if U64.eq vp 0UL then true else U64.eq vp hd_addr)
             then SA.alloc_search_found_head 's fp vp vcur (U64.v wz) (U64.v vfuel)
             else SA.alloc_search_found_prev 's fp vp vcur (U64.v wz) (U64.v vfuel));
            res_p := vp;
            res_c := vcur;
            go := false
          }
        } else {
          let vp = !prev_fp;
          SH.hd_address_spec (vcur <: obj_addr);
          SA.alloc_search_advance 's fp vp vcur (U64.v wz) (U64.v vfuel);
          prev_fp := vcur;
          cur_fp := next;
          fuel_ref := U64.sub vfuel 1UL;
          fuel_bound_lemma vfuel
        }
      }
    }
  };
  let p = !res_p;
  let c = !res_c;
  (p, c)
}
#pop-options

/// ---------------------------------------------------------------------------
/// Allocation from one list
/// ---------------------------------------------------------------------------

/// An unchanged entry leaves the state unchanged.
let fls_set_same (fls: FLs.fl_state) (i: nat)
  : Lemma (requires i < Seq.length fls)
          (ensures FLs.fls_set fls i (FLs.fls_head fls i) == fls)
  = Seq.lemma_eq_intro (FLs.fls_set fls i (FLs.fls_head fls i)) fls

/// `SAL.alloc_on`: first fit on list `i`, and, when the remainder's class is
/// no longer `i`, the block unlinked and its remainder pushed on its own list.
#push-options "--z3rlimit 120"
fn alloc_on_impl (heap: heap_t) (heads: array U64.t) (i: SZ.t) (wz: U64.t{U64.v wz >= 1})
  requires is_heap heap 's ** pts_to heads 'fls **
           pure (U64.v wz >= 1 /\ Seq.length 'fls == SC.n_lists /\ SZ.v i < SC.n_lists)
  returns obj: U64.t
  ensures exists* s2 fls2. is_heap heap s2 ** pts_to heads fls2 **
    pure (let r = SAL.alloc_on 's 'fls (SZ.v i) (U64.v wz) in
          s2 == r.SAL.heap_out /\ fls2 == r.SAL.fls_out /\ obj == r.SAL.obj_out /\
          Seq.length fls2 == SC.n_lists)
{
  let fp = heads.(i);
  assert (pure (fp == FLs.fls_head 'fls (SZ.v i)));
  let pc = find_fit heap fp wz;
  let p = fst pc;
  let c = snd pc;
  if (c = 0UL) {
    0UL
  } else {
    SAL.first_fit_same_block 's fp 0UL fp (U64.v wz) SpecBase.heap_words;
    SAL.search_at 's fp 0UL fp (U64.v wz) (U64.v wz) SpecBase.heap_words;
    hd_address_eq c;
    let hd_addr = hd_address c;
    SH.hd_address_spec (c <: obj_addr);
    let hdr = read_word heap hd_addr;
    let w = getWosize hdr;
    getWosize_eq hdr;
    let leftover = U64.sub w wz;
    rightjust_no_overflow hd_addr leftover;
    let alloc_hd_off = U64.add hd_addr (U64.mul leftover mword);
    let alloc_obj = U64.add alloc_hd_off mword;
    let next = read_word heap c;
    SA.spec_next_fp_eq 's (c <: obj_addr);
    // `p` is 0 or a word address, so it is a usable predecessor exactly when
    // it is not 0 and not the block's header (`SAL.pv`)
    let p_ok = (if U64.eq p 0UL then false else not (U64.eq p hd_addr));
    assert (pure (p_ok == SAL.pv p (c <: obj_addr)));
    let relist = (if U64.gte leftover 2UL
                  then not (SZ.eq (GC.Impl.FreeLists.class_of (U64.sub leftover 1UL)) i)
                  else false);
    assert (pure (relist == SAL.relists (SZ.v i) (U64.v w) (U64.v wz)));
    if (not relist) {
      // first fit on one list (`SAL.alloc_on_plain`)
      SAL.alloc_on_plain 's 'fls (SZ.v i) (U64.v wz);
      if U64.gte leftover 1UL {
        let new_fp = (if U64.gte leftover 2UL then c else next);
        assert (pure (new_fp == SA.alloc_replacement_fp 's (c <: obj_addr) (U64.v wz) next));
        let rem_hdr = makeHeader (U64.sub leftover 1UL) blue 0UL;
        let alloc_hdr = makeHeader wz white 0UL;
        if p_ok {
          write_word heap (p <: hp_addr) new_fp;
          prev_write_keeps_header 's (p <: hp_addr) hd_addr new_fp;
          SA.alloc_from_block_split_normal
            (SH.write_word 's (p <: hp_addr) new_fp) (c <: obj_addr) (U64.v wz) next;
          write_word heap hd_addr rem_hdr;
          write_word heap alloc_hd_off alloc_hdr;
          fls_set_same 'fls (SZ.v i);
          alloc_obj
        } else {
          SA.alloc_from_block_split_normal 's (c <: obj_addr) (U64.v wz) next;
          write_word heap hd_addr rem_hdr;
          write_word heap alloc_hd_off alloc_hdr;
          heads.(i) <- new_fp;
          alloc_obj
        }
      } else {
        let alloc_hdr = makeHeader wz white 0UL;
        if p_ok {
          write_word heap (p <: hp_addr) next;
          prev_write_keeps_header 's (p <: hp_addr) hd_addr next;
          SA.alloc_from_block_exact
            (SH.write_word 's (p <: hp_addr) next) (c <: obj_addr) (U64.v wz) next;
          write_word heap hd_addr alloc_hdr;
          fls_set_same 'fls (SZ.v i);
          alloc_obj
        } else {
          SA.alloc_from_block_exact 's (c <: obj_addr) (U64.v wz) next;
          write_word heap hd_addr alloc_hdr;
          heads.(i) <- next;
          alloc_obj
        }
      }
    } else {
      // the remainder moves (`SAL.relist_writes`)
      SAL.relist_writes 's 'fls (SZ.v i) (U64.v wz);
      let rc = GC.Impl.FreeLists.class_of (U64.sub leftover 1UL);
      let rem_hdr = makeHeader (U64.sub leftover 1UL) blue 0UL;
      let alloc_hdr = makeHeader wz white 0UL;
      let old = heads.(rc);
      if p_ok {
        write_word heap (p <: hp_addr) next;
        write_word heap hd_addr rem_hdr;
        write_word heap alloc_hd_off alloc_hdr;
        write_word heap c old;
        fls_set_same 'fls (SZ.v i);
        heads.(rc) <- c;
        alloc_obj
      } else {
        write_word heap hd_addr rem_hdr;
        write_word heap alloc_hd_off alloc_hdr;
        write_word heap c old;
        heads.(i) <- next;
        heads.(rc) <- c;
        alloc_obj
      }
    }
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// The allocator over the free-list heads
/// ---------------------------------------------------------------------------

/// An empty list has nothing to allocate.
let alloc_on_empty (g: SpecBase.heap) (fls: FLs.fl_state) (i: nat) (wz: pos)
  : Lemma (requires FLs.fls_head fls i == 0UL)
          (ensures (SAL.alloc_on g fls i wz).SAL.obj_out == 0UL /\
                   (SAL.alloc_on g fls i wz).SAL.heap_out == g /\
                   (SAL.alloc_on g fls i wz).SAL.fls_out == fls)
  = SA.alloc_search_invalid g 0UL 0UL 0UL wz SpecBase.heap_words

fn init_heap (heap: heap_t) (heads: array U64.t)
  requires is_heap heap 's ** pts_to heads 'fls **
           pure (Seq.length 'fls == SC.n_lists)
  ensures exists* s2 fls2. is_heap heap s2 ** pts_to heads fls2 **
    pure ((s2, fls2) == SAL.init_heap_lists_spec 's)
{
  let fp = init_heap_single heap;
  GC.Impl.FreeLists.clear_heads heads;
  if (fp = 0UL) {
    ()
  } else {
    let total_words = U64.div heap_size_u64 mword;
    let k = GC.Impl.FreeLists.class_of (U64.sub total_words 1UL);
    heads.(k) <- fp
  }
}

/// `SAL.alloc_lists_spec`: the small lists from the request's own upwards,
/// skipping empty ones, then list 0.
#push-options "--z3rlimit 80"
fn alloc_lists_impl (heap: heap_t) (heads: array U64.t) (wz: U64.t)
  requires is_heap heap 's ** pts_to heads 'fls **
           pure (U64.v wz >= 1 /\ Seq.length 'fls == SC.n_lists)
  returns obj: U64.t
  ensures exists* s2 fls2. is_heap heap s2 ** pts_to heads fls2 **
    pure (let r = SAL.alloc_lists_spec 's 'fls (U64.v wz) in
          s2 == r.SAL.heap_out /\ fls2 == r.SAL.fls_out /\ obj == r.SAL.obj_out)
{
  SC.n_lists_sz_v ();
  SC.n_small_u64_v ();
  let start = GC.Impl.FreeLists.class_of wz;
  SC.size_class_lt (U64.v wz);
  let mut i = start;
  let mut res = 0UL;
  let mut go = (SZ.gt start 0sz);
  while (!go)
    invariant exists* vgo vi vres s fls.
      R.pts_to go vgo **
      R.pts_to i vi **
      R.pts_to res vres **
      is_heap heap s ** pts_to heads fls **
      pure (
        Seq.length fls == SC.n_lists /\
        SZ.v vi <= SC.n_lists /\
        (if vgo then
           s == 's /\ fls == 'fls /\ vres == 0UL /\
           1 <= SZ.v vi /\ SZ.v vi <= SC.n_small /\
           SAL.alloc_from 's 'fls (U64.v wz) (SZ.v start) ==
             SAL.alloc_from 's 'fls (U64.v wz) (SZ.v vi)
         else
           (vres <> 0UL ==>
              (let r = SAL.alloc_from 's 'fls (U64.v wz) (SZ.v start) in
               s == r.SAL.heap_out /\ fls == r.SAL.fls_out /\ vres == r.SAL.obj_out)) /\
           (vres == 0UL ==>
              s == 's /\ fls == 'fls /\
              SAL.alloc_from 's 'fls (U64.v wz) (SZ.v start) ==
                SAL.alloc_on 's 'fls 0 (U64.v wz))))
    decreases (SC.n_lists - SZ.v !i + (if !go then 1 else 0))
  {
    let vi = !i;
    let h = heads.(vi);
    if (h = 0UL) {
      // an empty list: nothing to search
      alloc_on_empty 's 'fls (SZ.v vi) (U64.v wz);
      SAL.alloc_from_step 's 'fls (U64.v wz) (SZ.v vi);
      let ni = SZ.add vi 1sz;
      i := ni;
      if (SZ.gt ni (SZ.uint64_to_sizet SC.n_small_u64)) {
        go := false
      }
    } else {
      let o = alloc_on_impl heap heads vi wz;
      if (o <> 0UL) {
        res := o;
        go := false
      } else {
        SAL.alloc_on_zero 's 'fls (SZ.v vi) (U64.v wz);
        SAL.alloc_from_step 's 'fls (U64.v wz) (SZ.v vi);
        let ni = SZ.add vi 1sz;
        i := ni;
        if (SZ.gt ni (SZ.uint64_to_sizet SC.n_small_u64)) {
          go := false
        }
      }
    }
  };
  let vres = !res;
  if (vres = 0UL) {
    let h0 = heads.(0sz);
    if (h0 = 0UL) {
      alloc_on_empty 's 'fls 0 (U64.v wz);
      0UL
    } else {
      alloc_on_impl heap heads 0sz wz
    }
  } else {
    vres
  }
}
#pop-options

fn allocate (heap: heap_t) (heads: array U64.t) (wosize: U64.t)
  requires is_heap heap 's ** pts_to heads 'fls **
           pure (SF.well_formed_heap 's /\
                 U64.v wosize >= 1 /\
                 Seq.length 'fls == SC.n_lists)
  returns obj: U64.t
  ensures exists* s2 fls2. is_heap heap s2 ** pts_to heads fls2 **
    pure (let spec_res = SAL.alloc_lists_spec 's 'fls (U64.v wosize) in
          s2 == spec_res.heap_out /\
          fls2 == spec_res.fls_out /\
          obj == spec_res.obj_out)
{
  alloc_lists_impl heap heads wosize
}

fn allocate_part1 (heap: heap_t) (heads: array U64.t) (wosize: U64.t)
  requires is_heap heap 's ** pts_to heads 'fls **
           pure (SF.well_formed_heap_part1 's /\
                 FLs.fls_valid 's 'fls /\
                 FLs.fls_terminates 's 'fls /\
                 U64.v wosize >= 1 /\
                 Seq.length 'fls == SC.n_lists)
  returns obj: U64.t
  ensures exists* s2 fls2. is_heap heap s2 ** pts_to heads fls2 **
    pure (let spec_res = SAL.alloc_lists_spec 's 'fls (U64.v wosize) in
          s2 == spec_res.heap_out /\
          fls2 == spec_res.fls_out /\
          obj == spec_res.obj_out)
{
  alloc_lists_impl heap heads wosize
}
