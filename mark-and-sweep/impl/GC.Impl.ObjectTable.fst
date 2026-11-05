(*
   Pulse GC - Object-start table

   The table is an array of one entry per 64 KB window of the major heap
   (GC.Spec.ObjectTable).  This module holds its three writers' common part:

   - `emit_impl`: write one value into the entries from window `k` whose
     boundary is below `h` (GC.Spec.ObjectTable.emit).  The window index
     `k` and its boundary `nb` live in the caller's registers, so a call
     that writes nothing is one compare.
   - `table_alloc_write`: the entries of a newly allocated object
     (GC.Spec.ObjectTable.alloc_table).
   - `rebuild_walk`: the table of a heap, by walking it once (used when the
     heap is initialised).
*)

module GC.Impl.ObjectTable

#lang-pulse

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module R = Pulse.Lib.Reference
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SH = GC.Spec.Heap
module SF = GC.Spec.Fields
module OT = GC.Spec.ObjectTable

/// `emit`: from window `k` (boundary `nb`), write `v` while the boundary is
/// below `h`.  No window test is needed: a boundary below `h <= heap_size`
/// belongs to a window of the table (`OT.emit_step`).
inline_for_extraction
fn emit_impl (tbl: array U64.t) (k: R.ref U64.t) (nb: R.ref U64.t) (v: U64.t) (h: U64.t)
  requires pts_to tbl 't ** R.pts_to k 'k ** R.pts_to nb 'nb **
           pure (Seq.length 't == OT.n_windows /\ U64.v 'k <= OT.n_windows /\
                 U64.v 'nb == OT.boundary (U64.v 'k) /\ U64.v h <= heap_size)
  ensures exists* t2 k2 nb2. pts_to tbl t2 ** R.pts_to k k2 ** R.pts_to nb nb2 **
          pure (let e = OT.emit 't (U64.v 'k) v (U64.v h) in
                t2 == fst e /\ U64.v k2 == snd e /\
                U64.v nb2 == OT.boundary (U64.v k2) /\
                Seq.length t2 == OT.n_windows /\ U64.v k2 <= OT.n_windows)
{
  OT.emit_spec 't (U64.v 'k) v (U64.v h);
  while (U64.lt !nb h)
    invariant exists* vk vnb t1.
      pts_to tbl t1 ** R.pts_to k vk ** R.pts_to nb vnb **
      pure (Seq.length t1 == OT.n_windows /\ U64.v vk <= OT.n_windows /\
            U64.v vnb == OT.boundary (U64.v vk) /\
            OT.emit t1 (U64.v vk) v (U64.v h) == OT.emit 't (U64.v 'k) v (U64.v h))
    decreases (OT.n_windows - U64.v !k)
  {
    let vk = !k;
    let vnb = !nb;
    with t1. assert (pts_to tbl t1);
    OT.emit_step t1 (U64.v vk) v (U64.v h);
    OT.boundary_bound (U64.v vk);
    tbl.(SZ.uint64_to_sizet vk) <- v;
    k := U64.add vk 1UL;
    nb := U64.add vnb OT.window_bytes_u64
  };
  with t1 vk vnb. assert (pts_to tbl t1 ** R.pts_to k vk ** R.pts_to nb vnb);
  assert (pure (U64.v vnb >= U64.v h));
  OT.emit_stop t1 (U64.v vk) v (U64.v h);
  assert (pure (OT.emit t1 (U64.v vk) v (U64.v h) == (t1, U64.v vk)));
  assert (pure (OT.emit 't (U64.v 'k) v (U64.v h) == (t1, U64.v vk)))
}

/// The entries of an object just allocated at `obj` (0: none) for `wz` words.
/// An object with no boundary inside costs one compare; one with boundaries
/// first reads the entry past them (`OT.alloc_stale`).
inline_for_extraction
fn table_alloc_write (tbl: array U64.t) (obj: U64.t) (wz: U64.t)
  requires pts_to tbl 't **
           pure (Seq.length 't == OT.n_windows /\
                 (U64.v obj >= 8 ==> U64.v wz < pow2 54) /\
                 (obj == 0UL \/
                  (U64.v obj >= 8 /\ U64.v obj < heap_size /\ U64.v obj % 8 == 0)))
  ensures exists* t2. pts_to tbl t2 **
          pure (t2 == OT.alloc_table 't obj (U64.v wz) /\ Seq.length t2 == OT.n_windows)
{
  if (U64.lt obj (U64.add zero_addr 8UL)) {
    ()
  } else {
    assert (pure (U64.v obj >= U64.v zero_addr + 8 /\ U64.v obj < heap_size));
    let hp = U64.sub obj 8UL;
    let d = U64.sub hp zero_addr;
    assert (pure (U64.v d < heap_size));
    assert_norm (pow2 57 + 65535 < pow2 64);
    let j0 = U64.div (U64.add d 0xFFFFUL) OT.window_bytes_u64;
    OT.first_window_le (U64.v hp);
    OT.boundary_bound (U64.v j0);
    let nb0 = U64.add zero_addr (U64.mul j0 OT.window_bytes_u64);
    assert_norm (pow2 54 == 18014398509481984);
    assert_norm (pow2 57 == 144115188075855872);
    assert_norm (pow2 64 == 18446744073709551616);
    assert (pure (U64.v wz * 8 < pow2 57));
    let p_end = U64.add obj (U64.mul wz 8UL);
    let lim = (if U64.gte (U64.add p_end 8UL) heap_size_u64 then heap_size_u64 else p_end);
    assert (pure (U64.v lim == OT.new_block_limit (U64.v obj + U64.v wz * 8)));
    if (U64.lt nb0 lim) {
      // The object contains a boundary.  The guard: the first window past
      // it, `k1`, must not name a block below `hp`.
      let k1 = U64.div (U64.add (U64.sub lim zero_addr) 0xFFFFUL) OT.window_bytes_u64;
      assert (pure (U64.v k1 == OT.alloc_stop (U64.v obj + U64.v wz * 8)));
      OT.first_window_le (U64.v lim);
      OT.boundary_bound (U64.v k1);
      OT.boundary_lt (U64.v k1);
      let nb1 = U64.add zero_addr (U64.mul k1 OT.window_bytes_u64);
      let stale =
        (if U64.lt nb1 heap_size_u64 then U64.lt (tbl.(SZ.uint64_to_sizet k1)) hp else false);
      assert (pure (stale == OT.alloc_stale 't hp (U64.v obj + U64.v wz * 8)));
      if stale {
        ()
      } else {
        let mut k = j0;
        let mut nb = nb0;
        emit_impl tbl k nb hp lim;
        OT.emit_spec 't (U64.v j0) hp (U64.v lim)
      }
    } else {
      // No boundary inside: the writes are none, guard or not.
      OT.emit_stop 't (U64.v j0) hp (U64.v lim);
      OT.emit_spec 't (U64.v j0) hp (U64.v lim)
    }
  }
}

/// The table of the heap as it is, by one walk.
#push-options "--z3rlimit 60"
fn rebuild_walk (heap: heap_t) (tbl: array U64.t)
  requires is_heap heap 's ** pts_to tbl 't ** pure (Seq.length 't == OT.n_windows)
  ensures exists* t2. is_heap heap 's ** pts_to tbl t2 ** pure (OT.table_matches 's t2)
{
  OT.cursor_matches 's 't;
  OT.objs_from_zero 's;
  let mut cur = (zero_addr <: U64.t);
  let mut prev = (zero_addr <: U64.t);
  let mut k = 0UL;
  let mut nb = (zero_addr <: U64.t);
  let mut go = true;
  while (!go)
    invariant exists* vgo vcur vprev vk vnb t1.
      R.pts_to go vgo ** R.pts_to cur vcur ** R.pts_to prev vprev **
      R.pts_to k vk ** R.pts_to nb vnb ** pts_to tbl t1 ** is_heap heap 's **
      pure (Seq.length t1 == OT.n_windows /\ U64.v vk <= OT.n_windows /\
            U64.v vnb == OT.boundary (U64.v vk) /\
            U64.v vcur <= heap_size /\ U64.v vcur % 8 == 0 /\
            OT.cursor (OT.objs_from 's (U64.v vcur)) vprev (U64.v vk) t1 ==
              OT.cursor (SF.objects zero_addr 's) zero_addr 0 't /\
            (not vgo ==> OT.objs_from 's (U64.v vcur) == Seq.empty))
    decreases (heap_size - U64.v !cur + (if !go then 1 else 0))
  {
    let c = !cur;
    assert_norm (pow2 57 == 144115188075855872);
    if (U64.lt (U64.add c 8UL) heap_size_u64) {
      let hdr = read_word heap (c <: hp_addr);
      let wz = getWosize hdr;
      getWosize_eq hdr;
      assert_norm (pow2 54 == 18014398509481984);
      assert_norm (pow2 57 == 144115188075855872);
      assert_norm (pow2 64 == 18446744073709551616);
      let next = U64.add c (U64.mul (U64.add wz 1UL) 8UL);
      if (U64.gt next heap_size_u64) {
        OT.objs_from_stop 's (U64.v c);
        go := false
      } else {
        let vprev = !prev;
        with t1. assert (pts_to tbl t1);
        U64.v_inj (GC.Spec.Base.mk_hp_addr (U64.v c)) c;
        OT.cursor_walk_step 's c vprev (U64.v !k) t1;
        emit_impl tbl k nb vprev c;
        prev := c;
        cur := next
      }
    } else {
      OT.objs_from_stop 's (U64.v c);
      go := false
    }
  };
  let vprev = !prev;
  with t1. assert (pts_to tbl t1);
  OT.cursor_empty vprev (U64.v !k) t1;
  emit_impl tbl k nb vprev heap_size_u64
}
#pop-options
