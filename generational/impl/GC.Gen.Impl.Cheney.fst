(*
   Pulse GC (Generational) - Cheney BFS Promote Implementation

   Implements Cheney-style forward-on-discovery BFS:
   1. Forward each root (promote if unforwarded minor object)
   2. Scan queue: for each queued object, forward its minor children
   3. Returns when queue is exhausted — only reachable objects promoted

   Reuses promote_one from GC.Gen.Impl.Promote for actual object promotion.

   Ghost state: threads a CheneySpec.cheney_state through loop invariants
   to prove impl output matches the functional spec (cheney_promote).
*)

module GC.Gen.Impl.Cheney

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
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
module Sim = GC.Gen.Cheney.Sim
module SimOne = GC.Gen.Cheney.SimOne
module GR = Pulse.Lib.GhostReference

/// Max queue size = max minor objects = fwd_array_size
/// Spec-only: used in ghost assertions. Not extracted.
noextract
let queue_size : pos = fwd_array_size

/// Queue size as SizeT (uses uint64_to_sizet for clean C extraction)
let queue_size_sz : n:SZ.t{SZ.v n == queue_size} =
  SZ.uint64_to_sizet (U64.div minor_heap_size_u64 8UL)

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

/// Helper: if minor_wf and wosize == 0, addr is not a minor object
let not_minor_if_wosize_zero (ms: minor_state) (addr: U64.t)
  : Lemma (requires minor_wf ms /\ minor_wosize ms addr == 0)
          (ensures ~(Seq.mem addr (minor_objects ms)))
  = FStar.Classical.move_requires (minor_objects_body_bound ms) addr

/// Helper: when promote_object returns 0 (using minor_wosize as arg), heap/fp unchanged.
/// This matches the promote_one postcondition's use of minor_wosize.
let promote_one_oom_unchanged (ms: minor_state) (major: heap) (addr: U64.t) (fp: U64.t)
  : Lemma (requires minor_wosize ms addr > 0 /\
                    (PromoteSpec.promote_object ms major addr fp (minor_wosize ms addr)).new_addr == 0UL)
          (ensures (PromoteSpec.promote_object ms major addr fp (minor_wosize ms addr)).major_out == major /\
                   (PromoteSpec.promote_object ms major addr fp (minor_wosize ms addr)).fp_out == fp)
  = Sim.promote_object_zero_noop ms major addr fp (minor_wosize ms addr)

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
///
/// Ghost: proves output matches cheney_forward_one applied to ghost pre-state.

#push-options "--z3rlimit 160 --fuel 0 --ifuel 0 --split_queries no"
inline_for_extraction
fn forward_if_minor
  (minor: minor_heap_t) (major: heap_t) (fp_ref: R.ref U64.t)
  (fwd_arr: array U64.t)
  (queue: array U64.t) (back: R.ref SZ.t)
  (addr: U64.t)
  (#cs_pre: Ghost.erased CheneySpec.cheney_state)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           pts_to fwd_arr 'farr **
           pts_to queue 'q **
           R.pts_to back 'bk **
           pure (let minor_st : minor_state = {data='md; bump='mb} in
                 SF.well_formed_heap_part1 'ms /\
                 AllocLemmas.fl_valid 'ms 'fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 'ms 'fp (heap_size / U64.v mword) /\
                 Seq.length 'farr == fwd_array_size /\
                 Seq.length 'q == queue_size /\
                 SZ.v 'bk <= queue_size /\
                 minor_wf minor_st /\
                  minor_guards_complete minor_st /\
                 Seq.length (minor_objects minor_st) <= queue_size /\
                 Sim.impl_matches_spec 'ms 'fp 'farr 'q (SZ.v 'bk) cs_pre /\
                 SimOne.cheney_bfs_inv minor_st cs_pre)
  ensures exists* md2 mb2 ms2 fp2 farr2 q2 bk2.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    R.pts_to fp_ref fp2 **
    pts_to fwd_arr farr2 **
    pts_to queue q2 **
    R.pts_to back bk2 **
    pure (let minor_st : minor_state = {data='md; bump='mb} in
          let cs_post = CheneySpec.cheney_forward_one minor_st cs_pre addr in
          md2 == 'md /\ mb2 == 'mb /\
          SF.well_formed_heap_part1 ms2 /\
          AllocLemmas.fl_valid ms2 fp2 (heap_size / U64.v mword) /\
          AllocLemmas.fl_chain_terminates ms2 fp2 (heap_size / U64.v mword) /\
          Seq.length farr2 == fwd_array_size /\
          Seq.length q2 == queue_size /\
          SZ.v bk2 <= queue_size /\
          SZ.v bk2 >= SZ.v 'bk /\
          SZ.v bk2 <= SZ.v 'bk + 1 /\
          Sim.impl_matches_spec ms2 fp2 farr2 q2 (SZ.v bk2) cs_post /\
          SimOne.cheney_bfs_inv minor_st cs_post)
{
  // Check: is addr a valid minor object address?
  if U64.lt addr 8UL {
    // addr < 8 → not a minor object → spec is noop
    Sim.not_minor_if_guards_fail ({data='md; bump='mb} <: minor_state) addr;
    CheneySpec.cheney_forward_one_noop ({data='md; bump='mb} <: minor_state) cs_pre addr;
    SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr
  } else if U64.gte addr minor_heap_size_u64 {
    // addr >= minor_heap_size → not minor → noop
    Sim.not_minor_if_guards_fail ({data='md; bump='mb} <: minor_state) addr;
    CheneySpec.cheney_forward_one_noop ({data='md; bump='mb} <: minor_state) cs_pre addr;
    SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr
  } else if not (U64.eq (U64.rem addr 8UL) 0UL) {
    // addr not word-aligned → not minor → noop
    Sim.not_minor_if_guards_fail ({data='md; bump='mb} <: minor_state) addr;
    CheneySpec.cheney_forward_one_noop ({data='md; bump='mb} <: minor_state) cs_pre addr;
    SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr
  } else {
    // Check forwarding array: already forwarded?
    let idx = SZ.uint64_to_sizet (U64.div addr 8UL);
    let fwd_val = fwd_arr.(idx);
    if not (U64.eq fwd_val 0UL) {
      // Already forwarded: fwd_arr[addr/8] ≠ 0 → cs_fwd addr ≠ 0 → noop
      Sim.represents_fwd_read 'farr (cs_pre.CheneySpec.cs_fwd) addr;
      CheneySpec.cheney_forward_one_noop ({data='md; bump='mb} <: minor_state) cs_pre addr;
      SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr
    } else {
      // fwd_val == 0: establish cs_pre.cs_fwd addr = 0
      Sim.represents_fwd_read 'farr (cs_pre.CheneySpec.cs_fwd) addr;
      assert (pure ((cs_pre.CheneySpec.cs_fwd) addr == 0UL));
      // Valid unforwarded minor object — read wosize and bounds-check
      let wosize = read_minor_wosize minor addr;
      // Guard against overflow: wosize must be < minor_heap_size to safely multiply by 8
      if U64.gte wosize minor_heap_size_u64 {
        // wosize too large → contrapositive proves not minor → noop
        Sim.not_minor_if_wosize_bounds_fail ({data='md; bump='mb} <: minor_state) addr;
        CheneySpec.cheney_forward_one_noop ({data='md; bump='mb} <: minor_state) cs_pre addr;
        SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr
      } else {
      // Prove no overflow for wosize*8 and addr + wosize*8
      minor_arith_no_overflow (U64.v addr) (U64.v wosize);
      // Runtime bounds check: addr + wosize*8 must fit in minor heap
      if U64.gt (U64.add addr (U64.mul wosize 8UL)) minor_heap_size_u64 {
        // Bounds fail → contrapositive proves not minor → noop
        Sim.not_minor_if_wosize_bounds_fail ({data='md; bump='mb} <: minor_state) addr;
        CheneySpec.cheney_forward_one_noop ({data='md; bump='mb} <: minor_state) cs_pre addr;
        SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr
      } else {
      // All guards pass — promote
      // First establish membership if wosize > 0 (needed for spec lemmas)
      let new_addr = promote_one minor major fp_ref addr;
      if U64.eq new_addr 0UL {
        // OOM or wosize=0: promote returned 0 → spec is noop
        if U64.eq wosize 0UL {
          // wosize = 0 → addr ∉ minor_objects → cheney_forward_one is noop
          not_minor_if_wosize_zero ({data='md; bump='mb} <: minor_state) addr;
          CheneySpec.cheney_forward_one_noop ({data='md; bump='mb} <: minor_state) cs_pre addr;
          SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr
        } else {
          // wosize > 0, new_addr = 0 → OOM case
          // Establish addr ∈ minor_objects (guards all passed, wosize > 0)
          Sim.minor_guards_sufficient ({data='md; bump='mb} <: minor_state) addr;
          // promote_object returns 0 → noop_oom applies
          CheneySpec.cheney_forward_one_noop_oom ({data='md; bump='mb} <: minor_state) cs_pre addr;
          SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr
        }
      } else {
        // Success: addr is a valid minor object, promote succeeded
        Sim.minor_guards_sufficient ({data='md; bump='mb} <: minor_state) addr;
        // Now: Seq.mem addr (minor_objects minor_st), cs_fwd addr = 0,
        //      wosize > 0, promote_object.new_addr ≠ 0
        // So cheney_forward_one_success applies
        CheneySpec.cheney_forward_one_success ({data='md; bump='mb} <: minor_state) cs_pre addr;
        SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr;
        // Record forwarding
        fwd_arr.(idx) <- new_addr;
        // Prove forwarding array correspondence
        Sim.represents_fwd_update 'farr (cs_pre.CheneySpec.cs_fwd) addr new_addr;
        // Enqueue the minor address for scanning
        let bk = R.op_Bang back;
        if SZ.lt bk queue_size_sz {
          queue.(bk) <- addr;
          R.op_Colon_Equals back (SZ.add bk 1sz);
          // Prove queue correspondence after enqueue
          Sim.queue_update_correspondence 'q (cs_pre.CheneySpec.cs_queue) (SZ.v 'bk) addr
        } else {
          // Queue full — prove unreachable:
          // bfs_inv_strict_room: mem addr minor_objects /\ fwd addr = 0 →
          //   |cs_queue| < |minor_objects|
          // minor_objects_count_bound: |minor_objects| < minor_heap_size/8 == queue_size
          // impl_matches_spec: bk == |cs_queue|
          // So bk < queue_size — contradicts the else branch condition (bk >= queue_size)
          SimOne.cheney_bfs_inv_strict_room ({data='md; bump='mb} <: minor_state) cs_pre addr;
          minor_objects_count_bound ({data='md; bump='mb} <: minor_state);
          assert (pure False)
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
///
/// Ghost: uses a ghost reference to track cheney_state through the loop.
/// The equational invariant proves that after processing all roots,
/// the impl state matches cheney_forward_roots applied from cs0.

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
fn forward_roots
  (minor: minor_heap_t) (major: heap_t) (fp_ref: R.ref U64.t)
  (fwd_arr: array U64.t)
  (queue: array U64.t) (back: R.ref SZ.t)
  (roots: array U64.t) (nroots: SZ.t)
  (#cs0: Ghost.erased CheneySpec.cheney_state)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           pts_to fwd_arr 'farr **
           pts_to queue 'q **
           R.pts_to back 'bk **
           pts_to roots 'rs **
           pure (let minor_st : minor_state = {data='md; bump='mb} in
                 SF.well_formed_heap_part1 'ms /\
                 AllocLemmas.fl_valid 'ms 'fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 'ms 'fp (heap_size / U64.v mword) /\
                 Seq.length 'farr == fwd_array_size /\
                 Seq.length 'q == queue_size /\
                 SZ.v 'bk == 0 /\
                 SZ.v nroots == Seq.length 'rs /\
                 minor_wf minor_st /\
                  minor_guards_complete minor_st /\
                 Seq.length (minor_objects minor_st) <= queue_size /\
                 Sim.impl_matches_spec 'ms 'fp 'farr 'q (SZ.v 'bk) cs0 /\
                 SimOne.cheney_bfs_inv minor_st cs0)
  ensures exists* md2 mb2 ms2 fp2 farr2 q2 bk2 rs2.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    R.pts_to fp_ref fp2 **
    pts_to fwd_arr farr2 **
    pts_to queue q2 **
    R.pts_to back bk2 **
    pts_to roots rs2 **
    pure (let minor_st : minor_state = {data='md; bump='mb} in
          let cs1 = CheneySpec.cheney_forward_roots minor_st cs0 'rs 0 in
          md2 == 'md /\ mb2 == 'mb /\
          SF.well_formed_heap_part1 ms2 /\
          AllocLemmas.fl_valid ms2 fp2 (heap_size / U64.v mword) /\
          AllocLemmas.fl_chain_terminates ms2 fp2 (heap_size / U64.v mword) /\
          Seq.length farr2 == fwd_array_size /\
          Seq.length q2 == queue_size /\
          SZ.v bk2 <= queue_size /\
          rs2 == 'rs /\
          Sim.impl_matches_spec ms2 fp2 farr2 q2 (SZ.v bk2) cs1 /\
          SimOne.cheney_bfs_inv minor_st cs1)
{
  // Ghost reference tracks the spec state through the loop
  let gcs = GR.alloc (Ghost.reveal cs0);
  let mut i = 0sz;
  while (SZ.lt !i nroots)
    invariant exists* md_i mb_i ms_i fp_i farr_i q_i bk_i rs_i iv cs_i.
      is_minor minor md_i mb_i **
      is_heap major ms_i **
      R.pts_to fp_ref fp_i **
      pts_to fwd_arr farr_i **
      pts_to queue q_i **
      R.pts_to back bk_i **
      pts_to roots rs_i **
      R.pts_to i iv **
      GR.pts_to gcs cs_i **
      pure (let minor_st : minor_state = {data='md; bump='mb} in
            SZ.v iv <= SZ.v nroots /\
            md_i == 'md /\ mb_i == 'mb /\
            SF.well_formed_heap_part1 ms_i /\
            AllocLemmas.fl_valid ms_i fp_i (heap_size / U64.v mword) /\
            AllocLemmas.fl_chain_terminates ms_i fp_i (heap_size / U64.v mword) /\
            Seq.length farr_i == fwd_array_size /\
            Seq.length q_i == queue_size /\
            SZ.v bk_i <= queue_size /\
            SZ.v nroots == Seq.length 'rs /\
            rs_i == 'rs /\
            minor_wf minor_st /\
             minor_guards_complete minor_st /\
            Sim.impl_matches_spec ms_i fp_i farr_i q_i (SZ.v bk_i) cs_i /\
            SimOne.cheney_bfs_inv minor_st cs_i /\
            CheneySpec.cheney_forward_roots minor_st cs_i 'rs (SZ.v iv) ==
              CheneySpec.cheney_forward_roots minor_st cs0 'rs 0)
  {
    let iv = !i;
    let r = roots.(iv);
    // Read ghost state via ghost ref (accessible as function-level ghost in GR.op_Bang)
    let cs_cur = GR.op_Bang gcs;
    // Unfold spec equation: forward_roots cs_cur rs iv ==
    //   forward_one cs_cur (rs[iv]) then forward_roots cs' rs (iv+1)
    CheneySpec.cheney_forward_roots_step ({data='md; bump='mb} <: minor_state)
      (reveal cs_cur) 'rs (SZ.v iv);
    // Forward this root — postcondition gives cs_post = cheney_forward_one minor_st cs_cur r
    forward_if_minor minor major fp_ref fwd_arr queue back r #cs_cur;
    // Update ghost ref to the new spec state
    GR.op_Colon_Equals gcs
      (Ghost.hide (CheneySpec.cheney_forward_one ({data='md; bump='mb} <: minor_state)
        (reveal cs_cur) r));
    i := SZ.add iv 1sz
  };
  // At exit: iv == nroots == Seq.length 'rs
  // Read final ghost state and apply base case lemma
  let cs_final = GR.op_Bang gcs;
  CheneySpec.cheney_forward_roots_base ({data='md; bump='mb} <: minor_state)
    (reveal cs_final) 'rs (SZ.v nroots);
  GR.free gcs
}
#pop-options

/// ---------------------------------------------------------------------------
/// scan_loop: BFS scan of queued objects
/// ---------------------------------------------------------------------------
///
/// Ghost: uses ghost references to track scan state through nested loops.
/// Outer loop: ghost ref tracks the current cheney_state across queue entries.
/// Inner loop: separate ghost ref tracks state across fields of one object.

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
fn scan_loop
  (minor: minor_heap_t) (major: heap_t) (fp_ref: R.ref U64.t)
  (fwd_arr: array U64.t)
  (queue: array U64.t) (back: R.ref SZ.t)
  (#cs1: Ghost.erased CheneySpec.cheney_state)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           pts_to fwd_arr 'farr **
           pts_to queue 'q **
           R.pts_to back 'bk **
           pure (let minor_st : minor_state = {data='md; bump='mb} in
                 SF.well_formed_heap_part1 'ms /\
                 AllocLemmas.fl_valid 'ms 'fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 'ms 'fp (heap_size / U64.v mword) /\
                 Seq.length 'farr == fwd_array_size /\
                 Seq.length 'q == queue_size /\
                 SZ.v 'bk <= queue_size /\
                 minor_wf minor_st /\
                  minor_guards_complete minor_st /\
                 Seq.length (minor_objects minor_st) <= queue_size /\
                 Sim.impl_matches_spec 'ms 'fp 'farr 'q (SZ.v 'bk) cs1 /\
                 SimOne.cheney_bfs_inv minor_st cs1)
  ensures exists* md2 mb2 ms2 fp2 farr2 q2 bk2.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    R.pts_to fp_ref fp2 **
    pts_to fwd_arr farr2 **
    pts_to queue q2 **
    R.pts_to back bk2 **
    pure (let minor_st : minor_state = {data='md; bump='mb} in
          let cs_final = CheneySpec.cheney_scan minor_st cs1 0 (CheneySpec.cheney_fuel minor_st) in
          md2 == 'md /\ mb2 == 'mb /\
          SF.well_formed_heap_part1 ms2 /\
          AllocLemmas.fl_valid ms2 fp2 (heap_size / U64.v mword) /\
          AllocLemmas.fl_chain_terminates ms2 fp2 (heap_size / U64.v mword) /\
          Seq.length farr2 == fwd_array_size /\
          Seq.length q2 == queue_size /\
          SZ.v bk2 <= queue_size /\
          Sim.impl_matches_spec ms2 fp2 farr2 q2 (SZ.v bk2) cs_final /\
          SimOne.cheney_bfs_inv minor_st cs_final)
{
  let gcs = GR.alloc (Ghost.reveal cs1);
  let mut scan = 0sz;
  while (
    let s = !scan;
    let b = R.op_Bang back;
    SZ.lt s b
  )
    invariant exists* md_i mb_i ms_i fp_i farr_i q_i bk_i sv cs_s.
      is_minor minor md_i mb_i **
      is_heap major ms_i **
      R.pts_to fp_ref fp_i **
      pts_to fwd_arr farr_i **
      pts_to queue q_i **
      R.pts_to back bk_i **
      R.pts_to scan sv **
      GR.pts_to gcs cs_s **
      pure (let minor_st : minor_state = {data='md; bump='mb} in
            SZ.v sv <= SZ.v bk_i /\
            SZ.v bk_i <= queue_size /\
            md_i == 'md /\ mb_i == 'mb /\
            SF.well_formed_heap_part1 ms_i /\
            AllocLemmas.fl_valid ms_i fp_i (heap_size / U64.v mword) /\
            AllocLemmas.fl_chain_terminates ms_i fp_i (heap_size / U64.v mword) /\
            Seq.length farr_i == fwd_array_size /\
            Seq.length q_i == queue_size /\
            minor_wf minor_st /\
             minor_guards_complete minor_st /\
            Sim.impl_matches_spec ms_i fp_i farr_i q_i (SZ.v bk_i) cs_s /\
            SimOne.cheney_bfs_inv minor_st cs_s /\
            SZ.v sv <= CheneySpec.cheney_fuel minor_st /\
            CheneySpec.cheney_scan minor_st cs_s (SZ.v sv)
              (CheneySpec.cheney_fuel minor_st - SZ.v sv) ==
              CheneySpec.cheney_scan minor_st cs1 0 (CheneySpec.cheney_fuel minor_st))
  {
    let s = !scan;
    // Read the minor address at queue[scan]
    let obj = queue.(s);
    // Read current ghost state
    let cs_cur = GR.op_Bang gcs;
    // Establish: obj is a valid minor object (from BFS invariant + impl_matches_spec)
    SimOne.cheney_bfs_inv_valid ({data='md; bump='mb} <: minor_state) (reveal cs_cur);
    SimOne.queue_valid_elim ({data='md; bump='mb} <: minor_state)
      ((reveal cs_cur).CheneySpec.cs_queue);
    // Chain: obj = queue[s] = q[s] = cs_cur.cs_queue[s], and s < |cs_cur.cs_queue|
    assert (pure (SZ.v s < Seq.length ((reveal cs_cur).CheneySpec.cs_queue)));
    assert (pure (obj == Seq.index ((reveal cs_cur).CheneySpec.cs_queue) (SZ.v s)));
    assert (pure (Seq.mem obj (minor_objects ({data='md; bump='mb} <: minor_state))));
    minor_objects_valid ({data='md; bump='mb} <: minor_state) obj;
    minor_objects_body_bound ({data='md; bump='mb} <: minor_state) obj;
    // Now: obj >= 8, obj < minor_heap_size, obj % 8 == 0, wosize > 0, obj + wosize*8 <= mhs
    if U64.lt obj 8UL {
      // Unreachable: we proved obj >= 8
      scan := SZ.add s 1sz
    } else if U64.gte obj minor_heap_size_u64 {
      // Unreachable: we proved obj < minor_heap_size
      scan := SZ.add s 1sz
    } else if not (U64.eq (U64.rem obj 8UL) 0UL) {
      // Unreachable: we proved obj % 8 == 0
      scan := SZ.add s 1sz
    } else {
      let wosize = read_minor_wosize minor obj;
      if U64.gte wosize minor_heap_size_u64 {
        // Unreachable: we proved wosize < minor_heap_size
        scan := SZ.add s 1sz
      } else {
      minor_arith_no_overflow (U64.v obj) (U64.v wosize);
      if U64.gt (U64.add obj (U64.mul wosize 8UL)) minor_heap_size_u64 {
        // Unreachable: we proved obj + wosize*8 <= minor_heap_size
        scan := SZ.add s 1sz
      } else {
      // Establish scan_step preconditions:
      // s < |cs_queue| from loop condition + impl_matches_spec
      // cheney_fuel - s > 0: bfs_inv_bound gives |cs_queue| <= |minor_objects| == cheney_fuel
      SimOne.cheney_bfs_inv_bound ({data='md; bump='mb} <: minor_state) (reveal cs_cur);
      CheneySpec.cheney_fuel_eq ({data='md; bump='mb} <: minor_state);
      assert (pure (SZ.v s < Seq.length ((reveal cs_cur).CheneySpec.cs_queue)));
      assert (pure (CheneySpec.cheney_fuel ({data='md; bump='mb} <: minor_state) - SZ.v s > 0));
      // Unfold spec: cheney_scan_step for this queue entry
      CheneySpec.cheney_scan_step ({data='md; bump='mb} <: minor_state)
        (reveal cs_cur) (SZ.v s)
        (CheneySpec.cheney_fuel ({data='md; bump='mb} <: minor_state) - SZ.v s);
      // Inner field loop: forward each field of obj
      let gcs_f = GR.alloc (Ghost.reveal cs_cur);
      let mut field_idx = 0UL;
      while (U64.lt !field_idx wosize)
        invariant exists* md_f mb_f ms_f fp_f farr_f q_f bk_f fi cs_f.
          is_minor minor md_f mb_f **
          is_heap major ms_f **
          R.pts_to fp_ref fp_f **
          pts_to fwd_arr farr_f **
          pts_to queue q_f **
          R.pts_to back bk_f **
          R.pts_to field_idx fi **
          R.pts_to scan s **
          GR.pts_to gcs_f cs_f **
          pure (let minor_st : minor_state = {data='md; bump='mb} in
                U64.v fi <= U64.v wosize /\
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
                SZ.v s < SZ.v bk_f /\
                minor_wf minor_st /\
                 minor_guards_complete minor_st /\
                Sim.impl_matches_spec ms_f fp_f farr_f q_f (SZ.v bk_f) cs_f /\
                SimOne.cheney_bfs_inv minor_st cs_f /\
                CheneySpec.cheney_forward_fields minor_st cs_f obj (U64.v fi) (U64.v wosize) ==
                  CheneySpec.cheney_forward_fields minor_st (reveal cs_cur) obj 0 (U64.v wosize))
      {
        let fi = !field_idx;
        assert (pure (U64.v fi < U64.v wosize));
        assert (pure (U64.v obj + U64.v wosize * 8 <= minor_heap_size));
        // Read current inner ghost state
        let cs_fcur = GR.op_Bang gcs_f;
        // Unfold spec: cheney_forward_fields_step
        CheneySpec.cheney_forward_fields_step ({data='md; bump='mb} <: minor_state)
          (reveal cs_fcur) obj (U64.v fi) (U64.v wosize);
        // Read field[fi] from minor heap
        let field_addr = U64.add obj (U64.mul fi 8UL);
        let child = minor_read minor field_addr;
        // Bridge: minor_read at impl level == minor_read_field at spec level
        Sim.minor_read_eq_field ({data='md; bump='mb} <: minor_state) obj (U64.v fi);
        // Forward this child — produces cs' = cheney_forward_one minor_st cs_fcur child
        forward_if_minor minor major fp_ref fwd_arr queue back child #cs_fcur;
        // Update inner ghost ref
        GR.op_Colon_Equals gcs_f
          (Ghost.hide (CheneySpec.cheney_forward_one ({data='md; bump='mb} <: minor_state)
            (reveal cs_fcur) child));
        field_idx := U64.add fi 1UL
      };
      // After inner loop: fi == wosize, so by cheney_forward_fields_base:
      let cs_fend = GR.op_Bang gcs_f;
      CheneySpec.cheney_forward_fields_base ({data='md; bump='mb} <: minor_state)
        (reveal cs_fend) obj (U64.v wosize) (U64.v wosize);
      GR.free gcs_f;
      // cs_fend == cheney_forward_fields minor cs_cur obj 0 wosize
      // Update outer ghost ref to new scan state
      GR.op_Colon_Equals gcs cs_fend;
      scan := SZ.add s 1sz
      }
      }
    }
  };
  // At exit: sv >= bk — scan exhausted
  let cs_end = GR.op_Bang gcs;
  CheneySpec.cheney_scan_base ({data='md; bump='mb} <: minor_state)
    (reveal cs_end) (SZ.v !scan)
    (CheneySpec.cheney_fuel ({data='md; bump='mb} <: minor_state) - SZ.v !scan);
  GR.free gcs
}
#pop-options

/// ---------------------------------------------------------------------------
/// cheney_promote_phase: full BFS promotion (forward roots + scan)
/// ---------------------------------------------------------------------------
///
/// Establishes initial ghost state, calls forward_roots and scan_loop,
/// then derives the spec correspondence from the ghost loop invariants.
/// No assume_ needed — the ghost state threading proves the connection.

#push-options "--z3rlimit 80 --fuel 0 --ifuel 0"
fn cheney_promote_phase
  (minor: minor_heap_t) (major: heap_t) (fp_ref: R.ref U64.t)
  (fwd_arr: array U64.t)
  (roots: array U64.t) (nroots: SZ.t)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           pts_to fwd_arr 'farr **
           pts_to roots 'rs **
           pure (let minor_st : minor_state = {data='md; bump='mb} in
                 SF.well_formed_heap 'ms /\
                 AllocLemmas.fl_valid 'ms 'fp (heap_size / U64.v mword) /\
                 AllocLemmas.fl_chain_terminates 'ms 'fp (heap_size / U64.v mword) /\
                 PromoteSpec.heap_objects_dense 'ms /\
                 PromoteSpec.chain_objects_blue 'ms 'fp /\
                 Seq.length 'farr == fwd_array_size /\
                 (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
                 SZ.v nroots == Seq.length 'rs /\
                 minor_wf minor_st /\
                  minor_guards_complete minor_st /\
                 Seq.length (SF.objects zero_addr 'ms) > 0)
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
          Seq.length (SF.objects zero_addr ms2) > 0 /\
          Seq.length farr2 == fwd_array_size /\
          rs2 == 'rs)
{
  // Allocate BFS queue on the stack
  let mut queue = [| 0UL; queue_size_sz |];
  let mut back = 0sz;

  // Help SMT: well_formed_heap implies well_formed_heap_part1
  wfh_implies_part1 'ms;

  // Establish initial ghost spec state
  // cs0 = { cs_major='ms; cs_fp='fp; cs_fwd=empty_forwarding; cs_queue=empty }
  Sim.represents_fwd_initial 'farr;
  SimOne.cheney_bfs_inv_initial ({data='md; bump='mb} <: minor_state)
    ({ CheneySpec.cs_major = 'ms; CheneySpec.cs_fp = 'fp;
       CheneySpec.cs_fwd = PromoteSpec.empty_forwarding;
       CheneySpec.cs_queue = Seq.empty } <: CheneySpec.cheney_state);

  // Phase 1: Forward all roots
  // Pre: impl_matches_spec 'ms 'fp 'farr q0 0 cs0, cheney_bfs_inv minor_st cs0
  // Establish: |minor_objects| <= queue_size (needed for BFS queue bound)
  minor_objects_count_bound ({data='md; bump='mb} <: minor_state);
  forward_roots minor major fp_ref fwd_arr queue back roots nroots
    #(Ghost.hide ({ CheneySpec.cs_major = 'ms; CheneySpec.cs_fp = 'fp;
                    CheneySpec.cs_fwd = PromoteSpec.empty_forwarding;
                    CheneySpec.cs_queue = Seq.empty } <: CheneySpec.cheney_state));

  // Post: impl matches cs1 = cheney_forward_roots minor_st cs0 'rs 0,
  //       cheney_bfs_inv minor_st cs1

  // Phase 2: BFS scan loop
  // Pre: impl_matches_spec ... cs1, cheney_bfs_inv minor_st cs1
  scan_loop minor major fp_ref fwd_arr queue back
    #(Ghost.hide (CheneySpec.cheney_forward_roots ({data='md; bump='mb} <: minor_state)
        ({ CheneySpec.cs_major = 'ms; CheneySpec.cs_fp = 'fp;
           CheneySpec.cs_fwd = PromoteSpec.empty_forwarding;
           CheneySpec.cs_queue = Seq.empty } <: CheneySpec.cheney_state)
        'rs 0));

  // Post: impl matches cs_final = cheney_scan minor_st cs1 0 (cheney_fuel minor_st),
  //       cheney_bfs_inv minor_st cs_final

  // Ghost: establish derived properties via spec preservation lemmas
  // cs_final == cheney_scan ... (cheney_forward_roots ... cs0 ... 0) 0 (cheney_fuel ...)
  // which is exactly cheney_promote's definition
  CheneySpec.cheney_promote_preserves_dense ({data='md; bump='mb} <: minor_state) 'ms 'fp 'rs;
  CheneySpec.cheney_promote_preserves_cob ({data='md; bump='mb} <: minor_state) 'ms 'fp 'rs;
  CheneySpec.cheney_promote_preserves_wfh_part1 ({data='md; bump='mb} <: minor_state) 'ms 'fp 'rs
}
#pop-options
