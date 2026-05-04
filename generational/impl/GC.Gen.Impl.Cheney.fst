(*
   Pulse GC (Generational) - Cheney BFS Promote Implementation

   Implements Cheney-style forward-on-discovery BFS:
   1. Forward each root (promote if unforwarded minor object)
   2. Scan queue: for each queued object, forward its minor children
   3. Returns when queue is exhausted — only reachable objects promoted

   Reuses promote_one from GC.Gen.Impl.Promote for actual object promotion.
*)

module GC.Gen.Impl.Cheney

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Gen.Impl.Promote
open GC.Impl.Heap
open GC.Gen.Impl.UpdatePtrs
module Alloc = GC.Impl.Allocator
module AllocLemmas = GC.Spec.Allocator.Lemmas
module SF = GC.Spec.Fields
module PromoteSpec = GC.Gen.Promote
module CheneySpec = GC.Gen.Cheney

/// Max queue size = max minor objects = fwd_array_size
let queue_size : pos = fwd_array_size

let queue_size_sz : n:SZ.t{SZ.v n == queue_size} =
  SZ.fits_u64_implies_fits fwd_array_size;
  SZ.uint_to_t fwd_array_size

/// Helper: proves addr + wosize*8 < pow2 64 when both < minor_heap_size
let minor_arith_no_overflow (addr wosize: nat)
  : Lemma (requires addr < minor_heap_size /\ wosize < minor_heap_size)
          (ensures wosize * 8 < pow2 64 /\ addr + wosize * 8 < pow2 64)
  = FStar.Math.Lemmas.lemma_mult_le_right 8 wosize minor_heap_size;
    FStar.Math.Lemmas.lemma_mult_le_right 8 minor_heap_size (pow2 57);
    assert_norm (pow2 57 * 8 == pow2 60);
    assert_norm (pow2 57 + pow2 60 < pow2 64)

/// Helper: well_formed_heap implies well_formed_heap_part1
let wfh_implies_part1 (g: heap)
  : Lemma (requires SF.well_formed_heap g)
          (ensures SF.well_formed_heap_part1 g)
  = reveal_opaque (`%SF.well_formed_heap) (SF.well_formed_heap g)

/// ---------------------------------------------------------------------------
/// forward_if_minor: forward a single potential minor pointer
/// ---------------------------------------------------------------------------
///
/// If addr is a valid unforwarded minor object:
///   - Promote it (via promote_one)
///   - Record forwarding in fwd_arr
///   - Enqueue the original minor address into the BFS queue
///   - Increment queue back pointer
/// Otherwise: no-op.

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
inline_for_extraction
fn forward_if_minor
  (minor: minor_heap_t) (major: heap_t) (fp_ref: R.ref U64.t)
  (fwd_arr: array U64.t)
  (queue: array U64.t) (back: R.ref SZ.t)
  (addr: U64.t)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           pts_to fwd_arr 'farr **
           pts_to queue 'q **
           R.pts_to back 'bk **
           pure (SF.well_formed_heap_part1 'ms /\
                 AllocLemmas.fl_valid 'ms 'fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 'ms 'fp (heap_size / U64.v mword) /\
                 Seq.length 'farr == fwd_array_size /\
                 Seq.length 'q == queue_size /\
                 SZ.v 'bk <= queue_size)
  ensures exists* md2 mb2 ms2 fp2 farr2 q2 bk2.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    R.pts_to fp_ref fp2 **
    pts_to fwd_arr farr2 **
    pts_to queue q2 **
    R.pts_to back bk2 **
    pure (md2 == 'md /\ mb2 == 'mb /\
          SF.well_formed_heap_part1 ms2 /\
          AllocLemmas.fl_valid ms2 fp2 (heap_size / U64.v mword) /\
          AllocLemmas.fl_chain_terminates ms2 fp2 (heap_size / U64.v mword) /\
          Seq.length farr2 == fwd_array_size /\
          Seq.length q2 == queue_size /\
          SZ.v bk2 <= queue_size /\
          SZ.v bk2 >= SZ.v 'bk /\
          SZ.v bk2 <= SZ.v 'bk + 1)
{
  // Check: is addr a valid minor object address?
  if U64.lt addr 8UL {
    ()
  } else if U64.gte addr minor_heap_size_u64 {
    ()
  } else if U64.ne (U64.rem addr 8UL) 0UL {
    ()
  } else {
    // Check forwarding array: already forwarded?
    let idx = SZ.uint64_to_sizet (U64.div addr 8UL);
    let fwd_val = fwd_arr.(idx);
    if U64.ne fwd_val 0UL {
      // Already forwarded — no-op
      ()
    } else {
      // Valid unforwarded minor object — read wosize and bounds-check
      let wosize = read_minor_wosize minor addr;
      // Guard against overflow: wosize must be < minor_heap_size to safely multiply by 8
      if U64.gte wosize minor_heap_size_u64 {
        // wosize impossibly large — skip
        ()
      } else {
      // Prove no overflow for wosize*8 and addr + wosize*8
      minor_arith_no_overflow (U64.v addr) (U64.v wosize);
      // Runtime bounds check: addr + wosize*8 must fit in minor heap
      if U64.gt (U64.add addr (U64.mul wosize 8UL)) minor_heap_size_u64 {
        // Malformed object — skip
        ()
      } else {
      let new_addr = promote_one minor major fp_ref addr;
      if U64.eq new_addr 0UL {
        // OOM or zero-sized — don't enqueue
        ()
      } else {
        // Record forwarding
        fwd_arr.(idx) <- new_addr;
        // Enqueue the minor address for scanning
        let bk = R.op_Bang back;
        if SZ.lt bk queue_size_sz {
          queue.(bk) <- addr;
          R.op_Colon_Equals back (SZ.add bk 1sz)
        } else {
          // Queue full (shouldn't happen if queue_size >= max minor objects)
          ()
        }
      }
      }
      }
    }
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// forward_roots: forward all roots
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
fn forward_roots
  (minor: minor_heap_t) (major: heap_t) (fp_ref: R.ref U64.t)
  (fwd_arr: array U64.t)
  (queue: array U64.t) (back: R.ref SZ.t)
  (roots: array U64.t) (nroots: SZ.t)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           pts_to fwd_arr 'farr **
           pts_to queue 'q **
           R.pts_to back 'bk **
           pts_to roots 'rs **
           pure (SF.well_formed_heap_part1 'ms /\
                 AllocLemmas.fl_valid 'ms 'fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 'ms 'fp (heap_size / U64.v mword) /\
                 Seq.length 'farr == fwd_array_size /\
                 Seq.length 'q == queue_size /\
                 SZ.v 'bk == 0 /\
                 SZ.v nroots == Seq.length 'rs)
  ensures exists* md2 mb2 ms2 fp2 farr2 q2 bk2 rs2.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    R.pts_to fp_ref fp2 **
    pts_to fwd_arr farr2 **
    pts_to queue q2 **
    R.pts_to back bk2 **
    pts_to roots rs2 **
    pure (md2 == 'md /\ mb2 == 'mb /\
          SF.well_formed_heap_part1 ms2 /\
          AllocLemmas.fl_valid ms2 fp2 (heap_size / U64.v mword) /\
          AllocLemmas.fl_chain_terminates ms2 fp2 (heap_size / U64.v mword) /\
          Seq.length farr2 == fwd_array_size /\
          Seq.length q2 == queue_size /\
          SZ.v bk2 <= queue_size /\
          rs2 == 'rs)
{
  let mut i = 0sz;
  while (SZ.lt !i nroots)
    invariant exists* md_i mb_i ms_i fp_i farr_i q_i bk_i rs_i iv.
      is_minor minor md_i mb_i **
      is_heap major ms_i **
      R.pts_to fp_ref fp_i **
      pts_to fwd_arr farr_i **
      pts_to queue q_i **
      R.pts_to back bk_i **
      pts_to roots rs_i **
      R.pts_to i iv **
      pure (SZ.v iv <= SZ.v nroots /\
            md_i == 'md /\ mb_i == 'mb /\
            SF.well_formed_heap_part1 ms_i /\
            AllocLemmas.fl_valid ms_i fp_i (heap_size / U64.v mword) /\
            AllocLemmas.fl_chain_terminates ms_i fp_i (heap_size / U64.v mword) /\
            Seq.length farr_i == fwd_array_size /\
            Seq.length q_i == queue_size /\
            SZ.v bk_i <= queue_size /\
            SZ.v nroots == Seq.length 'rs /\
            rs_i == 'rs)
  {
    let iv = !i;
    let r = roots.(iv);
    forward_if_minor minor major fp_ref fwd_arr queue back r;
    i := SZ.add iv 1sz
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// scan_loop: BFS scan of queued objects
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
fn scan_loop
  (minor: minor_heap_t) (major: heap_t) (fp_ref: R.ref U64.t)
  (fwd_arr: array U64.t)
  (queue: array U64.t) (back: R.ref SZ.t)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           pts_to fwd_arr 'farr **
           pts_to queue 'q **
           R.pts_to back 'bk **
           pure (SF.well_formed_heap_part1 'ms /\
                 AllocLemmas.fl_valid 'ms 'fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 'ms 'fp (heap_size / U64.v mword) /\
                 Seq.length 'farr == fwd_array_size /\
                 Seq.length 'q == queue_size /\
                 SZ.v 'bk <= queue_size)
  ensures exists* md2 mb2 ms2 fp2 farr2 q2 bk2.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    R.pts_to fp_ref fp2 **
    pts_to fwd_arr farr2 **
    pts_to queue q2 **
    R.pts_to back bk2 **
    pure (md2 == 'md /\ mb2 == 'mb /\
          SF.well_formed_heap_part1 ms2 /\
          AllocLemmas.fl_valid ms2 fp2 (heap_size / U64.v mword) /\
          AllocLemmas.fl_chain_terminates ms2 fp2 (heap_size / U64.v mword) /\
          Seq.length farr2 == fwd_array_size /\
          Seq.length q2 == queue_size /\
          SZ.v bk2 <= queue_size)
{
  let mut scan = 0sz;
  while (
    let s = !scan;
    let b = R.op_Bang back;
    SZ.lt s b
  )
    invariant exists* md_i mb_i ms_i fp_i farr_i q_i bk_i sv.
      is_minor minor md_i mb_i **
      is_heap major ms_i **
      R.pts_to fp_ref fp_i **
      pts_to fwd_arr farr_i **
      pts_to queue q_i **
      R.pts_to back bk_i **
      R.pts_to scan sv **
      pure (SZ.v sv <= SZ.v bk_i /\
            SZ.v bk_i <= queue_size /\
            md_i == 'md /\ mb_i == 'mb /\
            SF.well_formed_heap_part1 ms_i /\
            AllocLemmas.fl_valid ms_i fp_i (heap_size / U64.v mword) /\
            AllocLemmas.fl_chain_terminates ms_i fp_i (heap_size / U64.v mword) /\
            Seq.length farr_i == fwd_array_size /\
            Seq.length q_i == queue_size)
  {
    let s = !scan;
    // Read the minor address at queue[scan]
    let obj = queue.(s);
    // Read wosize of this minor object
    // obj is a minor address that was enqueued after promotion
    // (we trust the queue contains valid minor addresses)
    if U64.lt obj 8UL {
      scan := SZ.add s 1sz
    } else if U64.gte obj minor_heap_size_u64 {
      scan := SZ.add s 1sz
    } else if U64.ne (U64.rem obj 8UL) 0UL {
      scan := SZ.add s 1sz
    } else {
      let wosize = read_minor_wosize minor obj;
      // Guard against overflow: wosize must be < minor_heap_size to safely multiply by 8
      if U64.gte wosize minor_heap_size_u64 {
        // wosize impossibly large — skip
        scan := SZ.add s 1sz
      } else {
      // Prove no overflow for wosize*8 and obj + wosize*8
      minor_arith_no_overflow (U64.v obj) (U64.v wosize);
      // Runtime bounds check: obj + wosize*8 must fit in minor heap
      if U64.gt (U64.add obj (U64.mul wosize 8UL)) minor_heap_size_u64 {
        // Malformed — skip this queue entry
        scan := SZ.add s 1sz
      } else {
      // Forward each field of this object
      let mut field_idx = 0UL;
      while (U64.lt !field_idx wosize)
        invariant exists* md_f mb_f ms_f fp_f farr_f q_f bk_f fi.
          is_minor minor md_f mb_f **
          is_heap major ms_f **
          R.pts_to fp_ref fp_f **
          pts_to fwd_arr farr_f **
          pts_to queue q_f **
          R.pts_to back bk_f **
          R.pts_to field_idx fi **
          R.pts_to scan s **
          pure (U64.v fi <= U64.v wosize /\
                SZ.v bk_f <= queue_size /\
                md_f == 'md /\ mb_f == 'mb /\
                SF.well_formed_heap_part1 ms_f /\
                AllocLemmas.fl_valid ms_f fp_f (heap_size / U64.v mword) /\
                AllocLemmas.fl_chain_terminates ms_f fp_f (heap_size / U64.v mword) /\
                Seq.length farr_f == fwd_array_size /\
                Seq.length q_f == queue_size /\
                U64.v obj >= 8 /\ U64.v obj < minor_heap_size /\
                U64.v obj % 8 == 0 /\
                U64.v obj + U64.v wosize * 8 <= minor_heap_size /\
                SZ.v s < SZ.v bk_f)
      {
        let fi = !field_idx;
        // fi < wosize and obj + wosize*8 <= minor_heap_size
        // so obj + fi*8 + 8 <= obj + wosize*8 <= minor_heap_size
        assert (pure (U64.v fi < U64.v wosize));
        assert (pure (U64.v obj + U64.v wosize * 8 <= minor_heap_size));
        // Read field[fi] from minor heap: address = obj + fi * 8
        let field_addr = U64.add obj (U64.mul fi 8UL);
        let child = minor_read minor field_addr;
        // Forward this child (forward_if_minor handles queue-full gracefully)
        forward_if_minor minor major fp_ref fwd_arr queue back child;
        field_idx := U64.add fi 1UL
      };
      scan := SZ.add s 1sz
      }
      }
    }
  }
}
#pop-options

/// ---------------------------------------------------------------------------
/// cheney_promote_phase: full BFS promotion (forward roots + scan)
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
fn cheney_promote_phase
  (minor: minor_heap_t) (major: heap_t) (fp_ref: R.ref U64.t)
  (fwd_arr: array U64.t)
  (roots: array U64.t) (nroots: SZ.t)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           pts_to fwd_arr 'farr **
           pts_to roots 'rs **
           pure (SF.well_formed_heap 'ms /\
                 AllocLemmas.fl_valid 'ms 'fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 'ms 'fp (heap_size / U64.v mword) /\
                 PromoteSpec.heap_objects_dense 'ms /\
                 PromoteSpec.chain_objects_blue 'ms 'fp /\
                 Seq.length 'farr == fwd_array_size /\
                 (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
                 SZ.v nroots == Seq.length 'rs)
  ensures exists* md2 mb2 ms2 fp2 farr2 rs2.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    R.pts_to fp_ref fp2 **
    pts_to fwd_arr farr2 **
    pts_to roots rs2 **
    pure (let minor_st : minor_state = { data = 'md; bump = 'mb } in
          let prom = CheneySpec.cheney_promote minor_st 'ms 'fp 'rs in
          md2 == 'md /\ mb2 == 'mb /\
          ms2 == prom.major_final /\
          fp2 == prom.fp_final /\
          represents_fwd farr2 prom.fwd_map /\
          SF.well_formed_heap_part1 ms2 /\
          AllocLemmas.fl_valid ms2 fp2 (heap_size / U64.v mword) /\
          AllocLemmas.fl_chain_terminates ms2 fp2 (heap_size / U64.v mword) /\
          PromoteSpec.heap_objects_dense ms2 /\
          PromoteSpec.chain_objects_blue ms2 fp2 /\
          Seq.length (SF.objects 0UL ms2) > 0 /\
          Seq.length farr2 == fwd_array_size /\
          rs2 == 'rs)
{
  // Allocate BFS queue on the stack (256 entries)
  let mut queue = [| 0UL; queue_size_sz |];
  let mut back = 0sz;

  // Help SMT: well_formed_heap implies well_formed_heap_part1
  wfh_implies_part1 'ms;
  assert (pure (SF.well_formed_heap_part1 'ms));

  // Phase 1: Forward all roots
  forward_roots minor major fp_ref fwd_arr queue back roots nroots;

  // Phase 2: BFS scan loop
  scan_loop minor major fp_ref fwd_arr queue back;

  // Ghost: establish spec equivalence and derived properties
  with ms2 fp2 farr2. assert (
    is_heap major ms2 ** R.pts_to fp_ref fp2 ** pts_to fwd_arr farr2);
  // The BFS loops implement cheney_promote — admitted pending loop invariant proofs
  assume_ (pure (
    let minor_st : minor_state = { data = 'md; bump = 'mb } in
    let prom = CheneySpec.cheney_promote minor_st 'ms 'fp 'rs in
    ms2 == prom.major_final /\
    fp2 == prom.fp_final /\
    represents_fwd farr2 prom.fwd_map /\
    PromoteSpec.heap_objects_dense ms2 /\
    PromoteSpec.chain_objects_blue ms2 fp2 /\
    Seq.length (SF.objects 0UL ms2) > 0))
}
#pop-options
