(*
   Pulse GC - Parallel sweep, one segment

   The loop of GC.Impl.FusedSweepCoalesce, on one segment [lo, hi), owning
   only those bytes.  It follows the model's seg_aux step by step: free
   objects grow the leading run until the first survivor, and the current
   run after it; the first survivor is whitened without a flush; each later
   survivor flushes the current run against the local list, then is
   whitened.  The run pending at the end is returned unflushed.

   The proof keeps the model's state in GC.Spec.SweepPar.SegLoop.loop_inv:
   the segment's copy of the heap is a ghost whole heap whose bytes [lo, hi)
   are the ones this function owns (GC.Impl.HeapRange).  Every read and
   write lies in [lo, hi): headers are below the cursor, and the cursor
   stays below hi, because lo and hi are consecutive boundaries.
*)

module GC.Impl.SweepSegment

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsToRange
open GC.Impl.Heap
open GC.Impl.Object
open GC.Impl.Fields
open GC.Impl.HeapRange
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq
module SP = GC.Spec.SweepPar
module SL = GC.Spec.SweepPar.SegLoop
module SC = GC.Spec.Coalesce
module Header = GC.Lib.Header

/// The object whose header is at the cursor.
inline_for_extraction
let obj_of (c: U64.t{U64.v c % 8 == 0 /\ U64.v c + 8 < heap_size})
  : o:obj_addr{U64.v o == U64.v c + 8}
  = U64.add c mword

/// A run grown by one object of wosize wz.
inline_for_extraction
let grow (rw: U64.t{U64.v rw < pow2 54}) (wz: wosize)
  : r:U64.t{U64.v r == U64.v rw + U64.v wz + 1}
  = assert_norm (pow2 54 + pow2 54 < pow2 64);
    U64.add rw (U64.add wz 1UL)

fn sweep_segment
  (heap: heap_t)
  (lo: hp_addr)
  (hi: U64.t{U64.v lo < U64.v hi /\ U64.v hi <= heap_size})
  (#g: erased heap_state)
  (#bs: erased (list nat))
  requires is_heap_range heap (U64.v lo) (U64.v hi)
             (Seq.slice g (U64.v lo) (U64.v hi)) **
           pure (SP.fused_pre g /\
                 SP.valid_bounds g bs /\
                 List.Tot.memP (U64.v lo, U64.v hi) (SP.segments bs))
  returns r: seg_result
  ensures exists* s.
    is_heap_range heap (U64.v lo) (U64.v hi) s **
    pure (s == Seq.slice (SP.sweep_segment g lo (U64.v hi)).SP.sheap
                         (U64.v lo) (U64.v hi) /\
          result_matches r (SP.sweep_segment g lo (U64.v hi)))
{
  SL.loop_entry g bs lo hi;
  unfold is_heap_range;
  fold (heap_range heap (U64.v lo) (U64.v hi) g);

  let mut cur = (lo <: U64.t);
  let mut go = true;
  let mut seen = false;
  let mut lfb = 0UL;
  let mut lrw = 0UL;
  let mut cfb = 0UL;
  let mut crw = 0UL;
  let mut fp = 0UL;
  let mut has = false;
  let mut fl = 0UL;

  while (!go)
    invariant exists* c gv sn lf lr cf cr f hs l h.
      pts_to cur c ** pts_to go gv ** pts_to seen sn **
      pts_to lfb lf ** pts_to lrw lr ** pts_to cfb cf ** pts_to crw cr **
      pts_to fp f ** pts_to has hs ** pts_to fl l **
      heap_range heap (U64.v lo) (U64.v hi) h **
      pure (SL.loop_inv g lo (U64.v hi) c h sn lf lr cf cr f hs l /\
            U64.v c <= heap_size /\
            (gv == false ==> Seq.length (SP.seg_rest g (U64.v c) (U64.v hi)) == 0))
    decreases (heap_size + (if !go then 1 else 0) - U64.v !cur)
  {
    let c = !cur;
    let sn = !seen;
    let lf = !lfb;
    let lr = !lrw;
    let cf = !cfb;
    let cr = !crw;
    let f = !fp;
    let hs = !has;
    let l = !fl;
    with h. assert (heap_range heap (U64.v lo) (U64.v hi) h);
    SL.loop_facts g lo (U64.v hi) c h sn lf lr cf cr f hs l;
    if (U64.lt c hi && U64.lt (U64.add c mword) heap_size_u64) {
      SL.aligned_lt (U64.v c) (U64.v hi);
      let ca : hp_addr = c;
      let hdr = read_word_r heap ca;
      SL.loop_head g lo (U64.v hi) c h sn lf lr cf cr f hs l hdr;
      let wz = getWosize hdr;
      lemma_object_size_no_overflow (U64.v wz);
      lemma_address_add_no_overflow (U64.v c) ((U64.v wz + 1) * 8);
      let next = U64.add c (U64.mul (U64.add wz 1UL) mword);
      if (U64.lte next heap_size_u64) {
        let obj = obj_of c;
        if (Header.Black? (getColor hdr)) {
          if (sn) {
            // A later survivor: flush the current run, then whiten.
            let f' = flush_blue_r heap cf cr f;
            let hs' = (hs || not (U64.eq f' f));
            let l' = (if (not hs && not (U64.eq f' f)) then f' else l);
            SL.loop_black_seen g lo (U64.v hi) c h lf lr cf cr f hs l hdr obj next
              (fst (SC.flush_blue h cf (U64.v cr) f)) f' hs' l';
            makeWhite_r heap obj;
            has := hs';
            fl := l';
            fp := f';
            cfb := 0UL;
            crw := 0UL;
            cur := next
          } else {
            // The first survivor: whiten; the leading run stays unflushed.
            SL.loop_black_first g lo (U64.v hi) c h lf lr cf cr f hs l hdr obj next;
            makeWhite_r heap obj;
            seen := true;
            cfb := 0UL;
            crw := 0UL;
            cur := next
          }
        } else {
          // A free object joins the pending run.
          if (sn) {
            let nrw = grow cr wz;
            SL.loop_free g lo (U64.v hi) c h sn lf lr cf cr f hs l hdr obj next nrw;
            cfb := (if U64.eq cr 0UL then obj else cf);
            crw := nrw;
            cur := next
          } else {
            let nrw = grow lr wz;
            SL.loop_free g lo (U64.v hi) c h sn lf lr cf cr f hs l hdr obj next nrw;
            lfb := (if U64.eq lr 0UL then obj else lf);
            lrw := nrw;
            cur := next
          }
        }
      } else {
        go := false
      }
    } else {
      SL.loop_more g lo (U64.v hi) c h sn lf lr cf cr f hs l;
      go := false
    }
  };

  let c = !cur;
  let sn = !seen;
  let lf = !lfb;
  let lr = !lrw;
  let cf = !cfb;
  let cr = !crw;
  let f = !fp;
  let hs = !has;
  let l = !fl;
  with h. assert (heap_range heap (U64.v lo) (U64.v hi) h);
  SL.loop_exit g lo (U64.v hi) c h sn lf lr cf cr f hs l;
  unfold heap_range;
  fold (is_heap_range heap (U64.v lo) (U64.v hi) (Seq.slice h (U64.v lo) (U64.v hi)));
  // all_free, lead, trail, has_link, first_link, local_head
  Mkseg_result (not sn) lf lr cf cr hs l f
}
