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
module PArr = Pulse.Lib.Array
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
module CheneyBFS = GC.Gen.CheneyBFS
module Sim = GC.Gen.Cheney.Sim
module SimOne = GC.Gen.Cheney.SimOne
module GR = Pulse.Lib.GhostReference
module AllocProps = GC.Gen.AllocProps

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

let minor_tag_infix_not_minor_object (ms: minor_state) (addr: U64.t)
  : Lemma (requires minor_wf ms /\ minor_tag ms addr == 249)
          (ensures ~(Seq.mem addr (minor_objects ms)))
  =
    if Seq.mem addr (minor_objects ms) then begin
      minor_objects_not_infix ms addr;
      assert False
    end

/// Helper: infix fwd addition doesn't overflow: parent_fwd < heap_size < pow2 57
/// and delta < minor_heap_size < pow2 57, so sum < pow2 58 < pow2 64
let infix_fwd_no_overflow (parent_fwd delta: nat)
  : Lemma (requires parent_fwd < heap_size /\ delta < minor_heap_size)
          (ensures parent_fwd + delta < pow2 64)
  = assert_norm (pow2 57 + pow2 57 == pow2 58);
    assert_norm (pow2 58 < pow2 64)

/// Helper: promote_object.new_addr, when non-zero, is < heap_size
let promote_new_addr_bound (ms: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma (ensures (let res = PromoteSpec.promote_object ms major obj fp wz in
                    res.new_addr <> 0UL ==> U64.v res.new_addr < heap_size))
  = AllocProps.alloc_spec_obj_valid major fp wz

/// The promoted copy has room for the whole object, not merely its header.
///
/// Forwarding an interior pointer lands at `new_addr + delta`, where `delta` is
/// the interior object's offset inside its enclosing closure and so is smaller
/// than `wz * 8`.  This bound is therefore what rules out the failure arm of
/// the bounded guard in `cheney_forward_one`'s interior branch: after a
/// successful promotion the sum is always below `heap_size`.
let promote_new_addr_body_bound
  (ms: minor_state) (major: heap) (obj: U64.t) (fp: U64.t) (wz: nat{wz > 0})
  : Lemma (requires SF.well_formed_heap_part1 major /\
                    AllocLemmas.fl_valid major fp heap_words /\
                    AllocLemmas.fl_chain_terminates major fp heap_words)
          (ensures (let res = PromoteSpec.promote_object ms major obj fp wz in
                    res.new_addr <> 0UL ==> U64.v res.new_addr + wz * 8 <= heap_size))
  = AllocProps.alloc_spec_obj_body_within_heap major fp wz;
    AllocProps.alloc_spec_obj_wosize_part1 major fp wz

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

/// ---------------------------------------------------------------------------
/// forward_if_minor_infix: handle the infix sub-case of forward_if_minor
/// ---------------------------------------------------------------------------
/// Called when: addr >= 8, addr < minor_heap_size, addr % 8 == 0,
///              cs_pre.cs_fwd addr == 0, tag == 249 (infix sub-object)
///
/// Strategy: forward the parent closure (promote if needed), then record
/// infix forwarding as parent_fwd + (addr - parent).

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
inline_for_extraction
fn forward_if_minor_infix
  (minor: minor_heap_t) (major: heap_t) (fp_ref: R.ref U64.t)
  (fwd_arr: array U64.t)
  (queue: array U64.t) (back: R.ref SZ.t)
  (oom_ref: R.ref bool)
  (addr: U64.t)
  (#cs_pre: Ghost.erased CheneySpec.cheney_state)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           pts_to fwd_arr 'farr **
           pts_to queue 'q **
           R.pts_to back 'bk **
           R.pts_to oom_ref 'oom_in **
           pure (let minor_st : minor_state = {data='md; bump='mb} in
                 SF.well_formed_heap_part1 'ms /\
                 AllocLemmas.fl_valid 'ms 'fp heap_words /\
                 AllocLemmas.fl_chain_terminates 'ms 'fp heap_words /\
                 Seq.length 'farr == fwd_array_size /\
                 Seq.length 'q == queue_size /\
                 SZ.v 'bk <= queue_size /\
                 minor_wf minor_st /\
                 minor_guards_complete minor_st /\
                 minor_infix_wf minor_st /\
                 Seq.length (minor_objects minor_st) <= queue_size /\
                 Sim.impl_matches_spec 'ms 'fp 'farr 'q (SZ.v 'bk) cs_pre /\
                 SimOne.cheney_bfs_inv minor_st cs_pre /\
                 // addr is a valid aligned minor addr with fwd=0 and tag=249
                 U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\ U64.v addr % 8 == 0 /\
                 (cs_pre.CheneySpec.cs_fwd) addr == 0UL /\
                 minor_tag minor_st addr == 249)
  ensures exists* md2 mb2 ms2 fp2 farr2 q2 bk2 oom_out.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    R.pts_to fp_ref fp2 **
    pts_to fwd_arr farr2 **
    pts_to queue q2 **
    R.pts_to back bk2 **
    R.pts_to oom_ref oom_out **
    pure (let minor_st : minor_state = {data='md; bump='mb} in
          let cs_post = CheneySpec.cheney_forward_one minor_st cs_pre addr in
          md2 == 'md /\ mb2 == 'mb /\
          SF.well_formed_heap_part1 ms2 /\
          AllocLemmas.fl_valid ms2 fp2 heap_words /\
          AllocLemmas.fl_chain_terminates ms2 fp2 heap_words /\
          Seq.length farr2 == fwd_array_size /\
          Seq.length q2 == queue_size /\
          SZ.v bk2 <= queue_size /\
          SZ.v bk2 >= SZ.v 'bk /\
          SZ.v bk2 <= SZ.v 'bk + 1 /\
          Sim.impl_matches_spec ms2 fp2 farr2 q2 (SZ.v bk2) cs_post /\
          SimOne.cheney_bfs_inv minor_st cs_post /\
          ('oom_in == true ==> oom_out == true) /\
          (not 'oom_in /\ oom_out ==> CheneyBFS.promote_fails_for minor_st cs_pre addr) /\
          (not oom_out ==> CheneyBFS.addr_covered minor_st cs_post addr))
{
  minor_tag_infix_not_minor_object ({data='md; bump='mb} <: minor_state) addr;
  // Establish is_infix_in_minor and extract parent info from minor_infix_wf
  infix_parent_in_minor_objects ({data='md; bump='mb} <: minor_state) addr;
  infix_parent_value ({data='md; bump='mb} <: minor_state) addr;
  // Read wosize (encodes offset to parent for infix objects)
  let wosize = read_minor_wosize minor addr;
  // Compute parent = addr - wosize * 8
  minor_arith_no_overflow (U64.v addr) (U64.v wosize);
  let parent = U64.sub addr (U64.mul wosize 8UL);
  // parent == infix_parent ms addr — establish validity and body bounds
  minor_objects_valid ({data='md; bump='mb} <: minor_state) parent;
  minor_objects_body_bound ({data='md; bump='mb} <: minor_state) parent;
  // Check if parent already forwarded
  let parent_idx = SZ.uint64_to_sizet (U64.div parent 8UL);
  let parent_fwd_val = fwd_arr.(parent_idx);
  Sim.represents_fwd_read 'farr (cs_pre.CheneySpec.cs_fwd) parent;
  let idx = SZ.uint64_to_sizet (U64.div addr 8UL);
  if not (U64.eq parent_fwd_val 0UL) {
    // Parent already forwarded: cheney_forward_normal(parent) is noop
    CheneySpec.cheney_forward_normal_noop ({data='md; bump='mb} <: minor_state) cs_pre parent;
    CheneySpec.cheney_forward_one_infix ({data='md; bump='mb} <: minor_state) cs_pre addr;
    SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr;
    CheneyBFS.addr_covered_infix_step ({data='md; bump='mb} <: minor_state) cs_pre addr;
    // Compute infix forwarding: parent_fwd + delta
    let delta = U64.sub addr parent;
    if U64.gte parent_fwd_val heap_size_u64 {
      // Guard fails: parent_fwd >= heap_size
      CheneySpec.cheney_forward_one_infix_guard_fail ({data='md; bump='mb} <: minor_state) cs_pre addr;
      ()
    } else {
      infix_fwd_no_overflow (U64.v parent_fwd_val) (U64.v delta);
      let sum = U64.add parent_fwd_val delta;
      if U64.lt sum heap_size_u64 {
        // Guard passes: record infix forwarding
        CheneySpec.cheney_forward_one_infix_guard_pass ({data='md; bump='mb} <: minor_state) cs_pre addr;
        fwd_arr.(idx) <- sum;
        Sim.represents_fwd_update 'farr (cs_pre.CheneySpec.cs_fwd) addr sum
      } else {
        // Guard failed: sum >= heap_size
        CheneySpec.cheney_forward_one_infix_guard_fail ({data='md; bump='mb} <: minor_state) cs_pre addr;
        ()
      }
    }
  } else {
    // Parent not yet forwarded: need to promote it
    let new_parent_addr = promote_one minor major fp_ref parent;
    if U64.eq new_parent_addr 0UL {
      // OOM: promote failed
      CheneySpec.cheney_forward_normal_noop_oom ({data='md; bump='mb} <: minor_state) cs_pre parent;
      CheneySpec.cheney_forward_one_infix_guard_fail ({data='md; bump='mb} <: minor_state) cs_pre addr;
      SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr;
      // The object that did not fit is the enclosing closure, not the infix
      // pointer itself: that is the second disjunct of `promote_fails_for`.
      assert (pure (CheneyBFS.promote_fails_at ({data='md; bump='mb} <: minor_state)
                      cs_pre (infix_parent ({data='md; bump='mb} <: minor_state) addr)));
      oom_ref := true
    } else {
      // Parent promoted successfully
      promote_new_addr_bound ({data='md; bump='mb} <: minor_state) 'ms parent 'fp
        (minor_wosize ({data='md; bump='mb} <: minor_state) parent);
      promote_new_addr_body_bound ({data='md; bump='mb} <: minor_state) 'ms parent 'fp
        (minor_wosize ({data='md; bump='mb} <: minor_state) parent);
      CheneySpec.cheney_forward_normal_success ({data='md; bump='mb} <: minor_state) cs_pre parent;
      // Record parent forwarding in fwd_arr
      fwd_arr.(parent_idx) <- new_parent_addr;
      Sim.represents_fwd_update 'farr (cs_pre.CheneySpec.cs_fwd) parent new_parent_addr;
      // Enqueue parent for scanning
      let bk = R.op_Bang back;
      Sim.cheney_bfs_inv_strict_room ({data='md; bump='mb} <: minor_state) cs_pre parent;
      minor_objects_count_bound ({data='md; bump='mb} <: minor_state);
      if SZ.lt bk queue_size_sz {
        queue.(bk) <- parent;
        R.op_Colon_Equals back (SZ.add bk 1sz);
        Sim.queue_update_correspondence 'q (cs_pre.CheneySpec.cs_queue) (SZ.v 'bk) parent;
        // impl_matches_spec now holds against cs' = cheney_forward_normal minor cs_pre parent
        CheneySpec.cheney_forward_one_infix ({data='md; bump='mb} <: minor_state) cs_pre addr;
        SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr;
        CheneyBFS.addr_covered_infix_step ({data='md; bump='mb} <: minor_state) cs_pre addr;
        // Compute infix fwd
        let delta = U64.sub addr parent;
        infix_fwd_no_overflow (U64.v new_parent_addr) (U64.v delta);
        let sum = U64.add new_parent_addr delta;
        if U64.lt sum heap_size_u64 {
          // Guard passes
          CheneySpec.cheney_forward_one_infix_guard_pass ({data='md; bump='mb} <: minor_state) cs_pre addr;
          let cs'_fwd : Ghost.erased PromoteSpec.forwarding_map =
            PromoteSpec.extend_forwarding (cs_pre.CheneySpec.cs_fwd) parent new_parent_addr;
          Sim.represents_fwd_update
            (Seq.upd 'farr (U64.v parent / 8) new_parent_addr)
            (reveal cs'_fwd) addr sum;
          fwd_arr.(idx) <- sum
        } else {
          // Unreachable: the promoted copy has room for the whole closure
          // (`promote_new_addr_body_bound`) and the interior offset stays
          // inside it (`infix_parent_in_minor_objects`), so the sum is below
          // `heap_size`.
          assert (pure False)
        }
      } else {
        // Queue full — prove unreachable via BFS invariant
        assert (pure False)
      }
    }
  }
}
#pop-options

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0 --z3smtopt '(set-option :smt.qi.eager_threshold 100)'"
inline_for_extraction
fn forward_if_minor
  (minor: minor_heap_t) (major: heap_t) (fp_ref: R.ref U64.t)
  (fwd_arr: array U64.t)
  (queue: array U64.t) (back: R.ref SZ.t)
  (oom_ref: R.ref bool)
  (addr: U64.t)
  (#cs_pre: Ghost.erased CheneySpec.cheney_state)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           pts_to fwd_arr 'farr **
           pts_to queue 'q **
           R.pts_to back 'bk **
           R.pts_to oom_ref 'oom_in **
           pure (let minor_st : minor_state = {data='md; bump='mb} in
                 SF.well_formed_heap_part1 'ms /\
                 AllocLemmas.fl_valid 'ms 'fp heap_words /\
                 AllocLemmas.fl_chain_terminates 'ms 'fp heap_words /\
                 Seq.length 'farr == fwd_array_size /\
                 Seq.length 'q == queue_size /\
                 SZ.v 'bk <= queue_size /\
                 minor_wf minor_st /\
                  minor_guards_complete minor_st /\
                  minor_infix_wf minor_st /\
                 Seq.length (minor_objects minor_st) <= queue_size /\
                 Sim.impl_matches_spec 'ms 'fp 'farr 'q (SZ.v 'bk) cs_pre /\
                 SimOne.cheney_bfs_inv minor_st cs_pre)
  ensures exists* md2 mb2 ms2 fp2 farr2 q2 bk2 oom_out.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    R.pts_to fp_ref fp2 **
    pts_to fwd_arr farr2 **
    pts_to queue q2 **
    R.pts_to back bk2 **
    R.pts_to oom_ref oom_out **
    pure (let minor_st : minor_state = {data='md; bump='mb} in
          let cs_post = CheneySpec.cheney_forward_one minor_st cs_pre addr in
          md2 == 'md /\ mb2 == 'mb /\
          SF.well_formed_heap_part1 ms2 /\
          AllocLemmas.fl_valid ms2 fp2 heap_words /\
          AllocLemmas.fl_chain_terminates ms2 fp2 heap_words /\
          Seq.length farr2 == fwd_array_size /\
          Seq.length q2 == queue_size /\
          SZ.v bk2 <= queue_size /\
          SZ.v bk2 >= SZ.v 'bk /\
          SZ.v bk2 <= SZ.v 'bk + 1 /\
          Sim.impl_matches_spec ms2 fp2 farr2 q2 (SZ.v bk2) cs_post /\
          SimOne.cheney_bfs_inv minor_st cs_post /\
          ('oom_in == true ==> oom_out == true) /\
          (not 'oom_in /\ oom_out ==> CheneyBFS.promote_fails_for minor_st cs_pre addr) /\
          (not oom_out ==> CheneyBFS.addr_covered minor_st cs_post addr))
{
  // Check: is addr a valid minor object address?
  if U64.lt addr 8UL {
    // addr < 8 → not a minor object → spec is noop
    Sim.not_minor_if_guards_fail ({data='md; bump='mb} <: minor_state) addr;
    CheneySpec.cheney_forward_one_noop ({data='md; bump='mb} <: minor_state) cs_pre addr;
    CheneyBFS.addr_covered_intro ({data='md; bump='mb} <: minor_state)
      (CheneySpec.cheney_forward_one ({data='md; bump='mb} <: minor_state) (Ghost.reveal cs_pre) addr) addr;
    SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr
  } else if U64.gte addr minor_heap_size_u64 {
    // addr >= minor_heap_size → not minor → noop
    Sim.not_minor_if_guards_fail ({data='md; bump='mb} <: minor_state) addr;
    CheneySpec.cheney_forward_one_noop ({data='md; bump='mb} <: minor_state) cs_pre addr;
    CheneyBFS.addr_covered_intro ({data='md; bump='mb} <: minor_state)
      (CheneySpec.cheney_forward_one ({data='md; bump='mb} <: minor_state) (Ghost.reveal cs_pre) addr) addr;
    SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr
  } else if not (U64.eq (U64.rem addr 8UL) 0UL) {
    // addr not word-aligned → not minor → noop
    Sim.not_minor_if_guards_fail ({data='md; bump='mb} <: minor_state) addr;
    CheneySpec.cheney_forward_one_noop ({data='md; bump='mb} <: minor_state) cs_pre addr;
    CheneyBFS.addr_covered_intro ({data='md; bump='mb} <: minor_state)
      (CheneySpec.cheney_forward_one ({data='md; bump='mb} <: minor_state) (Ghost.reveal cs_pre) addr) addr;
    SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr
  } else {
    // Check forwarding array: already forwarded?
    let idx = SZ.uint64_to_sizet (U64.div addr 8UL);
    let fwd_val = fwd_arr.(idx);
    if not (U64.eq fwd_val 0UL) {
      // Already forwarded: fwd_arr[addr/8] ≠ 0 → cs_fwd addr ≠ 0 → noop.
      // The address may be an interior pointer whose closure was forwarded on
      // an earlier visit, so coverage comes from the BFS invariant rather than
      // from anything this step does.
      Sim.represents_fwd_read 'farr (cs_pre.CheneySpec.cs_fwd) addr;
      CheneySpec.cheney_forward_one_noop ({data='md; bump='mb} <: minor_state) cs_pre addr;
      CheneyBFS.addr_covered_intro_forwarded ({data='md; bump='mb} <: minor_state)
        (CheneySpec.cheney_forward_one ({data='md; bump='mb} <: minor_state) (Ghost.reveal cs_pre) addr) addr;
      SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr
    } else {
      // fwd_val == 0: establish cs_pre.cs_fwd addr = 0
      Sim.represents_fwd_read 'farr (cs_pre.CheneySpec.cs_fwd) addr;
      assert (pure ((cs_pre.CheneySpec.cs_fwd) addr == 0UL));
      // Read tag to distinguish infix (tag=249) from normal objects
      let tag = read_minor_tag minor addr;
      if U64.eq tag 249UL {
        // INFIX CASE: delegate to helper
        forward_if_minor_infix minor major fp_ref fwd_arr queue back oom_ref addr #cs_pre
      } else {
      // NORMAL CASE: tag != 249, read wosize and proceed with existing logic
      let wosize = read_minor_wosize minor addr;
      // Guard against overflow: wosize must be < minor_heap_size to safely multiply by 8
      if U64.gte wosize minor_heap_size_u64 {
        // wosize too large → contrapositive proves not minor → noop
        Sim.not_minor_if_wosize_bounds_fail ({data='md; bump='mb} <: minor_state) addr;
        CheneySpec.cheney_forward_one_noop ({data='md; bump='mb} <: minor_state) cs_pre addr;
        CheneyBFS.addr_covered_intro ({data='md; bump='mb} <: minor_state)
          (CheneySpec.cheney_forward_one ({data='md; bump='mb} <: minor_state) (Ghost.reveal cs_pre) addr) addr;
        SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr
      } else {
      // Prove no overflow for wosize*8 and addr + wosize*8
      minor_arith_no_overflow (U64.v addr) (U64.v wosize);
      // Runtime bounds check: addr + wosize*8 must fit in minor heap
      if U64.gt (U64.add addr (U64.mul wosize 8UL)) minor_heap_size_u64 {
        // Bounds fail → contrapositive proves not minor → noop
        Sim.not_minor_if_wosize_bounds_fail ({data='md; bump='mb} <: minor_state) addr;
        CheneySpec.cheney_forward_one_noop ({data='md; bump='mb} <: minor_state) cs_pre addr;
        CheneyBFS.addr_covered_intro ({data='md; bump='mb} <: minor_state)
          (CheneySpec.cheney_forward_one ({data='md; bump='mb} <: minor_state) (Ghost.reveal cs_pre) addr) addr;
        SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr
      } else {
      // All guards pass — promote
      let new_addr = promote_one minor major fp_ref addr;
      if U64.eq new_addr 0UL {
        // OOM or wosize=0: promote returned 0 → spec is noop
        if U64.eq wosize 0UL {
          // wosize = 0 → addr ∉ minor_objects → cheney_forward_one is noop
          not_minor_if_wosize_zero ({data='md; bump='mb} <: minor_state) addr;
          CheneySpec.cheney_forward_one_noop ({data='md; bump='mb} <: minor_state) cs_pre addr;
          CheneyBFS.addr_covered_intro ({data='md; bump='mb} <: minor_state)
            (CheneySpec.cheney_forward_one ({data='md; bump='mb} <: minor_state) (Ghost.reveal cs_pre) addr) addr;
          SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr
        } else {
          // wosize > 0, new_addr = 0 → OOM case
          Sim.minor_guards_sufficient ({data='md; bump='mb} <: minor_state) addr;
          CheneySpec.cheney_forward_one_normal ({data='md; bump='mb} <: minor_state) cs_pre addr;
          CheneySpec.cheney_forward_normal_noop_oom ({data='md; bump='mb} <: minor_state) cs_pre addr;
          SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr;
          assert (pure (CheneyBFS.promote_fails_at ({data='md; bump='mb} <: minor_state)
                          cs_pre addr));
          // Signal OOM to caller
          oom_ref := true
        }
      } else {
        // Success: addr is a valid minor object, promote succeeded
        Sim.minor_guards_sufficient ({data='md; bump='mb} <: minor_state) addr;
        CheneySpec.cheney_forward_one_normal ({data='md; bump='mb} <: minor_state) cs_pre addr;
        CheneySpec.cheney_forward_normal_success ({data='md; bump='mb} <: minor_state) cs_pre addr;
        SimOne.fwd_one_preserves_bfs_inv ({data='md; bump='mb} <: minor_state) cs_pre addr;
        // Record forwarding
        fwd_arr.(idx) <- new_addr;
        // Prove forwarding array correspondence
        Sim.represents_fwd_update 'farr (cs_pre.CheneySpec.cs_fwd) addr new_addr;
        CheneyBFS.addr_covered_intro ({data='md; bump='mb} <: minor_state)
          (CheneySpec.cheney_forward_one ({data='md; bump='mb} <: minor_state) (Ghost.reveal cs_pre) addr) addr;
        // Enqueue the minor address for scanning
        let bk = R.op_Bang back;
        if SZ.lt bk queue_size_sz {
          queue.(bk) <- addr;
          R.op_Colon_Equals back (SZ.add bk 1sz);
          // Prove queue correspondence after enqueue
          Sim.queue_update_correspondence 'q (cs_pre.CheneySpec.cs_queue) (SZ.v 'bk) addr
        } else {
          // Queue full — prove unreachable
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
}
#pop-options

/// ---------------------------------------------------------------------------
/// forward_roots: forward all roots
/// ---------------------------------------------------------------------------
///
/// Ghost: uses a ghost reference to track cheney_state through the loop.
/// The equational invariant proves that after processing all roots,
/// the impl state matches cheney_forward_roots applied from cs0.

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
fn forward_roots
  (minor: minor_heap_t) (major: heap_t) (fp_ref: R.ref U64.t)
  (fwd_arr: array U64.t)
  (queue: array U64.t) (back: R.ref SZ.t)
  (oom_ref: R.ref bool)
  (roots: array U64.t) (nroots: SZ.t)
  (#cs0: Ghost.erased CheneySpec.cheney_state)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           pts_to fwd_arr 'farr **
           pts_to queue 'q **
           R.pts_to back 'bk **
           R.pts_to oom_ref 'oom_in **
           pts_to roots 'rs **
           pure (let minor_st : minor_state = {data='md; bump='mb} in
                 SF.well_formed_heap_part1 'ms /\
                 AllocLemmas.fl_valid 'ms 'fp heap_words /\
                 AllocLemmas.fl_chain_terminates 'ms 'fp heap_words /\
                 Seq.length 'farr == fwd_array_size /\
                 Seq.length 'q == queue_size /\
                 SZ.v 'bk == 0 /\
                 SZ.v nroots == Seq.length 'rs /\
                 minor_wf minor_st /\
                  minor_guards_complete minor_st /\
                  minor_infix_wf minor_st /\
                 Seq.length (minor_objects minor_st) <= queue_size /\
                 Sim.impl_matches_spec 'ms 'fp 'farr 'q (SZ.v 'bk) cs0 /\
                 SimOne.cheney_bfs_inv minor_st cs0)
  ensures exists* md2 mb2 ms2 fp2 farr2 q2 bk2 rs2 oom_out.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    R.pts_to fp_ref fp2 **
    pts_to fwd_arr farr2 **
    pts_to queue q2 **
    R.pts_to back bk2 **
    R.pts_to oom_ref oom_out **
    pts_to roots rs2 **
    pure (let minor_st : minor_state = {data='md; bump='mb} in
          let cs1 = CheneySpec.cheney_forward_roots minor_st cs0 'rs 0 in
          md2 == 'md /\ mb2 == 'mb /\
          SF.well_formed_heap_part1 ms2 /\
          AllocLemmas.fl_valid ms2 fp2 heap_words /\
          AllocLemmas.fl_chain_terminates ms2 fp2 heap_words /\
          Seq.length farr2 == fwd_array_size /\
          Seq.length q2 == queue_size /\
          SZ.v bk2 <= queue_size /\
          rs2 == 'rs /\
          Sim.impl_matches_spec ms2 fp2 farr2 q2 (SZ.v bk2) cs1 /\
          SimOne.cheney_bfs_inv minor_st cs1 /\
          ('oom_in == true ==> oom_out == true) /\
          (not 'oom_in /\ oom_out ==>
             CheneyBFS.cheney_oom_reaching minor_st
               (CheneySpec.cheney_scan minor_st cs1 0 (CheneySpec.cheney_fuel minor_st))) /\
          (not oom_out ==> CheneyBFS.fwd_covers_roots minor_st cs1.CheneySpec.cs_fwd 'rs))
{
  // Ghost reference tracks the spec state through the loop
  let gcs = GR.alloc (Ghost.reveal cs0);
  CheneyBFS.root_prefix_empty ({data='md; bump='mb} <: minor_state) (Ghost.reveal cs0) 'rs;
  let mut i = 0sz;
  while (SZ.lt !i nroots)
    invariant exists* md_i mb_i ms_i fp_i farr_i q_i bk_i rs_i iv cs_i oom_i.
      is_minor minor md_i mb_i **
      is_heap major ms_i **
      R.pts_to fp_ref fp_i **
      pts_to fwd_arr farr_i **
      pts_to queue q_i **
      R.pts_to back bk_i **
      R.pts_to oom_ref oom_i **
      pts_to roots rs_i **
      R.pts_to i iv **
      GR.pts_to gcs cs_i **
      pure (let minor_st : minor_state = {data='md; bump='mb} in
            SZ.v iv <= SZ.v nroots /\
            md_i == 'md /\ mb_i == 'mb /\
            SF.well_formed_heap_part1 ms_i /\
            AllocLemmas.fl_valid ms_i fp_i heap_words /\
            AllocLemmas.fl_chain_terminates ms_i fp_i heap_words /\
            Seq.length farr_i == fwd_array_size /\
            Seq.length q_i == queue_size /\
            SZ.v bk_i <= queue_size /\
            SZ.v nroots == Seq.length 'rs /\
            rs_i == 'rs /\
            minor_wf minor_st /\
             minor_guards_complete minor_st /\
            minor_infix_wf minor_st /\
            Sim.impl_matches_spec ms_i fp_i farr_i q_i (SZ.v bk_i) cs_i /\
            SimOne.cheney_bfs_inv minor_st cs_i /\
            ('oom_in == true ==> oom_i == true) /\
            (not 'oom_in /\ oom_i ==>
               CheneyBFS.cheney_oom_reaching minor_st
                 (CheneySpec.cheney_scan minor_st
                    (CheneySpec.cheney_forward_roots minor_st cs0 'rs 0) 0
                    (CheneySpec.cheney_fuel minor_st))) /\
            (not oom_i ==> CheneyBFS.root_prefix_covered minor_st cs_i 'rs (SZ.v iv)) /\
            CheneySpec.cheney_forward_roots minor_st cs_i 'rs (SZ.v iv) ==
              CheneySpec.cheney_forward_roots minor_st cs0 'rs 0)
    decreases (Prims.op_Subtraction (SZ.v nroots) (SZ.v !i))
  {
    let iv = !i;
    let r = roots.(iv);
    // Read ghost state via ghost ref (accessible as function-level ghost in GR.op_Bang)
    let cs_cur = GR.op_Bang gcs;
    // Unfold spec equation: forward_roots cs_cur rs iv ==
    //   forward_one cs_cur (rs[iv]) then forward_roots cs' rs (iv+1)
    CheneySpec.cheney_forward_roots_step ({data='md; bump='mb} <: minor_state)
      (reveal cs_cur) 'rs (SZ.v iv);
    let oom_before = !oom_ref;
    // Forward this root — postcondition gives cs_post = cheney_forward_one minor_st cs_cur r
    forward_if_minor minor major fp_ref fwd_arr queue back oom_ref r #cs_cur;
    let oom_after = !oom_ref;
    CheneyBFS.root_prefix_step_oom ({data='md; bump='mb} <: minor_state)
      (reveal cs_cur) 'rs (SZ.v iv) oom_before oom_after;
    CheneyBFS.cheney_oom_intro_root ({data='md; bump='mb} <: minor_state)
      (reveal cs_cur)
      (CheneySpec.cheney_scan ({data='md; bump='mb} <: minor_state)
         (CheneySpec.cheney_forward_roots ({data='md; bump='mb} <: minor_state) cs0 'rs 0) 0
         (CheneySpec.cheney_fuel ({data='md; bump='mb} <: minor_state)))
      'rs (SZ.v iv)
      (CheneySpec.cheney_fuel ({data='md; bump='mb} <: minor_state))
      oom_before oom_after;
    // Update ghost ref to the new spec state
    GR.op_Colon_Equals gcs
      (Ghost.hide (CheneySpec.cheney_forward_one ({data='md; bump='mb} <: minor_state)
        (reveal cs_cur) r));
    i := SZ.add iv 1sz
  };
  // At exit: iv == nroots == Seq.length 'rs
  // Read final ghost state and apply base case lemma
  let cs_final = GR.op_Bang gcs;
  assert (pure (SZ.v nroots == Seq.length 'rs));
  CheneySpec.cheney_forward_roots_base ({data='md; bump='mb} <: minor_state)
    (reveal cs_final) 'rs (SZ.v nroots);
  assert (pure (CheneySpec.cheney_forward_roots ({data='md; bump='mb} <: minor_state)
                  (reveal cs_final) 'rs (SZ.v nroots) == reveal cs_final));
  assert (pure (CheneySpec.cheney_forward_roots ({data='md; bump='mb} <: minor_state)
                  (reveal cs_final) 'rs (SZ.v nroots) ==
                CheneySpec.cheney_forward_roots ({data='md; bump='mb} <: minor_state)
                  cs0 'rs 0));
  let oom_final = !oom_ref;
  CheneyBFS.root_prefix_all_implies_covers_oom ({data='md; bump='mb} <: minor_state)
    (reveal cs_final) 'rs oom_final;
  assert (pure ((reveal cs_final) ==
    CheneySpec.cheney_forward_roots ({data='md; bump='mb} <: minor_state) cs0 'rs 0));
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

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
fn scan_loop
  (minor: minor_heap_t) (major: heap_t) (fp_ref: R.ref U64.t)
  (fwd_arr: array U64.t)
  (queue: array U64.t) (back: R.ref SZ.t)
  (oom_ref: R.ref bool)
  (#cs1: Ghost.erased CheneySpec.cheney_state)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           pts_to fwd_arr 'farr **
           pts_to queue 'q **
           R.pts_to back 'bk **
           R.pts_to oom_ref 'oom_in **
           pure (let minor_st : minor_state = {data='md; bump='mb} in
                 SF.well_formed_heap_part1 'ms /\
                 AllocLemmas.fl_valid 'ms 'fp heap_words /\
                 AllocLemmas.fl_chain_terminates 'ms 'fp heap_words /\
                 Seq.length 'farr == fwd_array_size /\
                 Seq.length 'q == queue_size /\
                 SZ.v 'bk <= queue_size /\
                 minor_wf minor_st /\
                  minor_guards_complete minor_st /\
                  minor_infix_wf minor_st /\
                 Seq.length (minor_objects minor_st) <= queue_size /\
                 Sim.impl_matches_spec 'ms 'fp 'farr 'q (SZ.v 'bk) cs1 /\
                 SimOne.cheney_bfs_inv minor_st cs1)
  ensures exists* md2 mb2 ms2 fp2 farr2 q2 bk2 oom_out.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    R.pts_to fp_ref fp2 **
    pts_to fwd_arr farr2 **
    pts_to queue q2 **
    R.pts_to back bk2 **
    R.pts_to oom_ref oom_out **
    pure (let minor_st : minor_state = {data='md; bump='mb} in
          let cs_final = CheneySpec.cheney_scan minor_st cs1 0 (CheneySpec.cheney_fuel minor_st) in
          md2 == 'md /\ mb2 == 'mb /\
          SF.well_formed_heap_part1 ms2 /\
          AllocLemmas.fl_valid ms2 fp2 heap_words /\
          AllocLemmas.fl_chain_terminates ms2 fp2 heap_words /\
          Seq.length farr2 == fwd_array_size /\
          Seq.length q2 == queue_size /\
          SZ.v bk2 <= queue_size /\
          Sim.impl_matches_spec ms2 fp2 farr2 q2 (SZ.v bk2) cs_final /\
          SimOne.cheney_bfs_inv minor_st cs_final /\
          ('oom_in == true ==> oom_out == true) /\
          (not 'oom_in /\ oom_out ==> CheneyBFS.cheney_oom_reaching minor_st cs_final) /\
          (not oom_out ==> CheneyBFS.fwd_closed minor_st cs_final.CheneySpec.cs_fwd))
{
  let gcs = GR.alloc (Ghost.reveal cs1);
  CheneyBFS.scanned_prefix_empty ({data='md; bump='mb} <: minor_state) (Ghost.reveal cs1);
  let mut scan = 0sz;
  while (
    let s = !scan;
    let b = R.op_Bang back;
    SZ.lt s b
  )
    invariant exists* md_i mb_i ms_i fp_i farr_i q_i bk_i sv cs_s oom_s.
      is_minor minor md_i mb_i **
      is_heap major ms_i **
      R.pts_to fp_ref fp_i **
      pts_to fwd_arr farr_i **
      pts_to queue q_i **
      R.pts_to back bk_i **
      R.pts_to oom_ref oom_s **
      R.pts_to scan sv **
      GR.pts_to gcs cs_s **
      pure (let minor_st : minor_state = {data='md; bump='mb} in
            SZ.v sv <= SZ.v bk_i /\
            SZ.v bk_i <= queue_size /\
            md_i == 'md /\ mb_i == 'mb /\
            SF.well_formed_heap_part1 ms_i /\
            AllocLemmas.fl_valid ms_i fp_i heap_words /\
            AllocLemmas.fl_chain_terminates ms_i fp_i heap_words /\
            Seq.length farr_i == fwd_array_size /\
            Seq.length q_i == queue_size /\
            minor_wf minor_st /\
             minor_guards_complete minor_st /\
            minor_infix_wf minor_st /\
            Sim.impl_matches_spec ms_i fp_i farr_i q_i (SZ.v bk_i) cs_s /\
            SimOne.cheney_bfs_inv minor_st cs_s /\
            ('oom_in == true ==> oom_s == true) /\
            (not 'oom_in /\ oom_s ==>
               CheneyBFS.cheney_oom_reaching minor_st
                 (CheneySpec.cheney_scan minor_st cs1 0 (CheneySpec.cheney_fuel minor_st))) /\
            (not oom_s ==> CheneyBFS.scanned_prefix_closed minor_st cs_s (SZ.v sv)) /\
            SZ.v sv <= CheneySpec.cheney_fuel minor_st /\
            CheneySpec.cheney_scan minor_st cs_s (SZ.v sv)
              (CheneySpec.cheney_fuel minor_st - SZ.v sv) ==
              CheneySpec.cheney_scan minor_st cs1 0 (CheneySpec.cheney_fuel minor_st))
    decreases (Prims.op_Subtraction queue_size (SZ.v !scan))
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
      let oom_s_before = !oom_ref;
      CheneyBFS.field_prefix_empty ({data='md; bump='mb} <: minor_state) (reveal cs_cur) obj;
      let mut field_idx = 0UL;
      while (U64.lt !field_idx wosize)
        invariant exists* md_f mb_f ms_f fp_f farr_f q_f bk_f fi cs_f oom_f.
          is_minor minor md_f mb_f **
          is_heap major ms_f **
          R.pts_to fp_ref fp_f **
          pts_to fwd_arr farr_f **
          pts_to queue q_f **
          R.pts_to back bk_f **
          R.pts_to oom_ref oom_f **
          R.pts_to field_idx fi **
          R.pts_to scan s **
          GR.pts_to gcs_f cs_f **
          pure (let minor_st : minor_state = {data='md; bump='mb} in
                U64.v fi <= U64.v wosize /\
                SZ.v bk_f <= queue_size /\
                md_f == 'md /\ mb_f == 'mb /\
                SF.well_formed_heap_part1 ms_f /\
                AllocLemmas.fl_valid ms_f fp_f heap_words /\
                AllocLemmas.fl_chain_terminates ms_f fp_f heap_words /\
                Seq.length farr_f == fwd_array_size /\
                Seq.length q_f == queue_size /\
                U64.v obj >= 8 /\ U64.v obj < minor_heap_size /\
                U64.v obj % 8 == 0 /\
                U64.v obj + U64.v wosize * 8 <= minor_heap_size /\
                SZ.v s < SZ.v bk_f /\
                minor_wf minor_st /\
                 minor_guards_complete minor_st /\
                 minor_infix_wf minor_st /\
                Sim.impl_matches_spec ms_f fp_f farr_f q_f (SZ.v bk_f) cs_f /\
                SimOne.cheney_bfs_inv minor_st cs_f /\
                ('oom_in == true ==> oom_f == true) /\
                (oom_s_before == true ==> oom_f == true) /\
                (not oom_s_before /\ oom_f ==>
                   CheneyBFS.cheney_oom_fields minor_st (reveal cs_cur) obj (U64.v wosize)) /\
                (not oom_f ==> CheneyBFS.field_prefix_covered minor_st cs_f obj (U64.v fi)) /\
                CheneySpec.cheney_forward_fields minor_st cs_f obj (U64.v fi) (U64.v wosize) ==
                  CheneySpec.cheney_forward_fields minor_st (reveal cs_cur) obj 0 (U64.v wosize))
        decreases (Prims.op_Subtraction (U64.v wosize) (U64.v !field_idx))
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
        let child_raw = minor_read minor field_addr;
        // Bridge: minor_read at impl level == minor_read_field at spec level
        Sim.minor_read_eq_field ({data='md; bump='mb} <: minor_state) obj (U64.v fi);
        assert (pure (child_raw == minor_read_field ({data='md; bump='mb} <: minor_state) obj (U64.v fi)));
        // Translate absolute minor address to offset
        let child = to_minor_offset_u64 child_raw;
        assert (pure (child == to_minor_offset child_raw));
        // Bridge: child == to_minor_offset (minor_read_field minor_st obj fi)
        assert (pure (child == to_minor_offset (minor_read_field ({data='md; bump='mb} <: minor_state) obj (U64.v fi))));
        // Forward this child — produces cs' = cheney_forward_one minor_st cs_fcur child
        let oom_before_child = !oom_ref;
        forward_if_minor minor major fp_ref fwd_arr queue back oom_ref child #cs_fcur;
        let oom_after_child = !oom_ref;
        CheneyBFS.field_prefix_step_oom ({data='md; bump='mb} <: minor_state)
          (reveal cs_fcur) obj (U64.v fi) oom_before_child oom_after_child;
        CheneyBFS.cheney_oom_intro_field ({data='md; bump='mb} <: minor_state)
          (reveal cs_cur) (reveal cs_fcur) obj (U64.v fi) (U64.v wosize)
          oom_before_child oom_after_child;
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
      let oom_s_after = !oom_ref;
      CheneyBFS.scanned_prefix_step_oom ({data='md; bump='mb} <: minor_state)
        (reveal cs_cur) (reveal cs_fend) (SZ.v s) oom_s_before oom_s_after;
      CheneyBFS.cheney_oom_fields_elim ({data='md; bump='mb} <: minor_state)
        (reveal cs_cur)
        (CheneySpec.cheney_scan ({data='md; bump='mb} <: minor_state) cs1 0
           (CheneySpec.cheney_fuel ({data='md; bump='mb} <: minor_state)))
        obj (U64.v wosize) (SZ.v s + 1)
        (CheneySpec.cheney_fuel ({data='md; bump='mb} <: minor_state) - SZ.v s - 1)
        oom_s_before oom_s_after;
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
  let oom_final = !oom_ref;
  assert (pure (SZ.v !scan >= Seq.length ((reveal cs_end).CheneySpec.cs_queue)));
  CheneyBFS.scanned_exhausted_implies_fwd_closed_oom ({data='md; bump='mb} <: minor_state)
    (reveal cs_end) (SZ.v !scan) oom_final;
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

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
fn cheney_promote_phase
  (minor: minor_heap_t) (major: heap_t) (fp_ref: R.ref U64.t)
  (fwd_arr: array U64.t)
  (queue: larray U64.t queue_size)
  (roots: array U64.t) (nroots: SZ.t)
  requires is_minor minor 'md 'mb **
           is_heap major 'ms **
           R.pts_to fp_ref 'fp **
           pts_to fwd_arr 'farr **
           pts_to queue 'qv **
           pts_to roots 'rs **
           pure (let minor_st : minor_state = {data='md; bump='mb} in
                 SF.well_formed_heap 'ms /\
                 AllocLemmas.fl_valid 'ms 'fp heap_words /\
                 AllocLemmas.fl_chain_terminates 'ms 'fp heap_words /\
                 PromoteSpec.heap_objects_dense 'ms /\
                 PromoteSpec.chain_objects_blue 'ms 'fp /\
                 Seq.length 'farr == fwd_array_size /\
                 (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
                 SZ.v nroots == Seq.length 'rs /\
                 minor_wf minor_st /\
                  minor_guards_complete minor_st /\
                  minor_infix_wf minor_st /\
                 Seq.length (SF.objects zero_addr 'ms) > 0)
  returns ok: bool
  ensures exists* md2 mb2 ms2 fp2 farr2 rs2 qv2.
    is_minor minor md2 mb2 **
    is_heap major ms2 **
    R.pts_to fp_ref fp2 **
    pts_to fwd_arr farr2 **
    pts_to queue qv2 **
    pts_to roots rs2 **
    pure (let minor_st : minor_state = { data = 'md; bump = 'mb } in
          let prom = CheneySpec.cheney_promote minor_st 'ms 'fp 'rs in
          md2 == 'md /\ mb2 == 'mb /\
          ms2 == prom.major_final /\
          fp2 == prom.fp_final /\
          represents_fwd farr2 prom.fwd_map /\
          SF.well_formed_heap_part1 ms2 /\
          AllocLemmas.fl_valid ms2 fp2 heap_words /\
          AllocLemmas.fl_chain_terminates ms2 fp2 heap_words /\
          PromoteSpec.heap_objects_dense ms2 /\
          PromoteSpec.chain_objects_blue ms2 fp2 /\
          Seq.length (SF.objects zero_addr ms2) > 0 /\
          Seq.length farr2 == fwd_array_size /\
          rs2 == 'rs /\
          (ok ==> CheneyBFS.cheney_no_oom minor_st 'ms 'fp 'rs) /\
          (not ok ==> CheneyBFS.cheney_oom minor_st 'ms 'fp 'rs))
{
  // Zero the BFS queue (heap-allocated, passed from caller)
  PArr.fill queue_size_sz queue 0UL;
  let mut back = 0sz;

  // OOM tracking flag
  let mut oom = false;

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
  forward_roots minor major fp_ref fwd_arr queue back oom roots nroots
    #(Ghost.hide ({ CheneySpec.cs_major = 'ms; CheneySpec.cs_fp = 'fp;
                    CheneySpec.cs_fwd = PromoteSpec.empty_forwarding;
                    CheneySpec.cs_queue = Seq.empty } <: CheneySpec.cheney_state));

  // Post: impl matches cs1 = cheney_forward_roots minor_st cs0 'rs 0,
  //       cheney_bfs_inv minor_st cs1
  let oom_after_roots = !oom;

  // Phase 2: BFS scan loop
  // Pre: impl_matches_spec ... cs1, cheney_bfs_inv minor_st cs1
  scan_loop minor major fp_ref fwd_arr queue back oom
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
  CheneySpec.cheney_promote_preserves_wfh_part1 ({data='md; bump='mb} <: minor_state) 'ms 'fp 'rs;

  // Return success (no OOM detected)
  let oom_val = !oom;
  CheneyBFS.cheney_no_oom_from_loop_posts
    ({data='md; bump='mb} <: minor_state) 'ms 'fp 'rs oom_after_roots oom_val;
  not oom_val
}
#pop-options
