/// ---------------------------------------------------------------------------
/// GC.Impl.Pages.Forward - the Cheney forwarding step with the page allocator
/// ---------------------------------------------------------------------------
///
/// Plan §30.  The forwarding step of akhil's `GC.Gen.Impl.Cheney`
/// (`forward_if_minor`: promote a nursery object, record it in the
/// forwarding array and queue it; an infix address through its closure),
/// with every copy allocated by `Pages.Promote.promote_one`: the page
/// allocator of the phase, for any allocator `a` that is that allocator
/// (`Sim.at_phase`).  It computes exactly the model's step,
/// `Spec.Pages.Promote.forward_one a`, and keeps the loop invariant; the
/// loops are in `GC.Impl.Pages.Cheney`.
///
/// The proof follows akhil's: a ghost copy of the model state.  It differs
/// in its shape:
///
///   * the Pulse state is one predicate, `cst ... cs` (the heap, the page
///     state, the forwarding array, the queue and its back are the model
///     state `cs`: `Sim.matches`), and the loop invariant is `Sim.sim`, both
///     abstract;
///   * the step is split by branch (`fwd_normal`, `fwd_infix`,
///     `fwd_infix_done`, `fwd_infix_new`; `forward_if_minor` only
///     dispatches), each closed by one lemma of `Promote.Sim`, so that every
///     query has one branch's facts;
///   * the queue cannot overflow (`Sim.sim_strict_room`), so there is no
///     run-time check for it; nor for the infix offset, which stays in its
///     closure's copy (`Sim.step_infix_fwd`, `step_infix_new`).

module GC.Impl.Pages.Forward

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Gen.ForwardingArray
open GC.Impl.Heap
open GC.Spec.Pages.Inv
open GC.Impl.Pages.State
open GC.Gen.Promote
open GC.Spec.Pages.Promote
open GC.Impl.Pages.Promote

module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq
module I = GC.Spec.AllocIface
module Sim = GC.Spec.Pages.Promote.Sim
module CSim = GC.Gen.Cheney.Sim
module L = GC.Spec.Pages.Promote.Loop

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The state
/// ---------------------------------------------------------------------------

/// The major heap, the page state, the forwarding array and the queue are
/// the model state `cs`.
let cst (major: heap_t) (t: pstate_t) (fwd_arr queue: array U64.t) (back: R.ref SZ.t)
        (cs: gstate pstate) : slprop =
  exists* (g: heap_state) (st: pstate) (farr q: Seq.seq U64.t) (bk: SZ.t).
    is_heap major g ** pages_st t st ** pts_to fwd_arr farr ** pts_to queue q ** R.pts_to back bk **
    pure (Sim.matches cs g st farr q (SZ.v bk))

/// What every step assumes: the allocator is the page allocator of `ph`,
/// the nursery's guards are complete, and the loop invariant holds.
/// The nursery's state.
let mst (d: minor_heap) (b: U64.t) : minor_state = {data = d; bump = b}

let pre (a: tal pstate) (ph: I.phase) (marking: bool) (ms: minor_state) (g0: heap) (cs: gstate pstate) : prop =
  Sim.at_phase a ph /\ marking == I.Marking? ph /\ minor_guards_complete ms /\ Sim.sim a ms g0 cs

/// akhil's: an address and a size in the nursery, times eight, do not overflow.
let minor_arith_no_overflow (addr wosize: nat)
  : Lemma (requires addr < minor_heap_size /\ wosize < minor_heap_size)
          (ensures wosize * 8 < pow2 64 /\ addr + wosize * 8 < pow2 64)
  = FStar.Math.Lemmas.lemma_mult_le_right 8 wosize minor_heap_size;
    FStar.Math.Lemmas.lemma_mult_le_right 8 minor_heap_size (pow2 57);
    assert_norm (pow2 57 * 8 == pow2 60);
    assert_norm (pow2 57 + pow2 60 < pow2 64)

/// A queue index fits a `size_t`.
let fits_queue (n: nat)
  : Lemma (requires n <= queue_size) (ensures SZ.fits n)
  = assert_norm (pow2 57 < pow2 64);
    SZ.fits_u64_implies_fits n

/// The forwarding entry of a nursery address.
inline_for_extraction
fn get_fwd (major: heap_t) (t: pstate_t) (fwd_arr queue: array U64.t) (back: R.ref SZ.t) (addr: U64.t)
  (#cs: erased (gstate pstate))
  requires cst major t fwd_arr queue back cs **
           pure (U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\ U64.v addr % 8 == 0)
  returns f: U64.t
  ensures cst major t fwd_arr queue back cs ** pure (f == cs.fwd addr)
{
  unfold cst;
  with g st farr q bk. assert (is_heap major g ** pages_st t st ** pts_to fwd_arr farr ** pts_to queue q ** R.pts_to back bk ** pure (Sim.matches cs g st farr q (SZ.v bk)));
  Sim.matches_fwd cs g st farr q (SZ.v bk) addr;
  let f = fwd_arr.(SZ.uint64_to_sizet (U64.div addr 8UL));
  fold (cst major t fwd_arr queue back cs);
  f
}

/// The back of the queue.
inline_for_extraction
fn get_back (major: heap_t) (t: pstate_t) (fwd_arr queue: array U64.t) (back: R.ref SZ.t)
  (#cs: erased (gstate pstate))
  requires cst major t fwd_arr queue back cs
  returns b: SZ.t
  ensures cst major t fwd_arr queue back cs **
          pure (SZ.v b == Seq.length cs.queue /\ SZ.v b <= queue_size)
{
  unfold cst;
  let b = !back;
  fold (cst major t fwd_arr queue back cs);
  b
}

/// The queue at `s`, below the back.
inline_for_extraction
fn get_queue (major: heap_t) (t: pstate_t) (fwd_arr queue: array U64.t) (back: R.ref SZ.t) (s: SZ.t)
  (#cs: erased (gstate pstate))
  requires cst major t fwd_arr queue back cs ** pure (SZ.v s < Seq.length cs.queue)
  returns x: U64.t
  ensures cst major t fwd_arr queue back cs **
          pure (SZ.v s < Seq.length cs.queue /\ x == Seq.index cs.queue (SZ.v s))
{
  unfold cst;
  with g st farr q bk. assert (is_heap major g ** pages_st t st ** pts_to fwd_arr farr ** pts_to queue q ** R.pts_to back bk ** pure (Sim.matches cs g st farr q (SZ.v bk)));
  Sim.matches_queue cs g st farr q (SZ.v bk) (SZ.v s);
  let x = queue.(s);
  fold (cst major t fwd_arr queue back cs);
  x
}

/// ---------------------------------------------------------------------------
/// The forwarding step, by branch
/// ---------------------------------------------------------------------------

/// A nursery object not yet forwarded: promote it, record it, queue it.
#push-options "--z3rlimit 30"
fn fwd_normal (minor: minor_heap_t) (major: heap_t) (t: pstate_t) (marking: bool)
  (fwd_arr queue: array U64.t) (back: R.ref SZ.t) (oom_ref: R.ref bool) (addr: U64.t) (wz: U64.t)
  (#a: erased (tal pstate)) (#ph: erased I.phase) (#g0: erased heap) (#cs: erased (gstate pstate))
  requires is_minor minor 'md 'mb ** cst major t fwd_arr queue back cs ** R.pts_to oom_ref 'oom **
           pure (pre a ph marking (mst 'md 'mb) g0 cs /\
                 Seq.mem addr (minor_objects (mst 'md 'mb)) /\ cs.fwd addr == 0UL /\
                 U64.v wz == minor_wosize (mst 'md 'mb) addr)
  ensures exists* oom'. is_minor minor 'md 'mb **
          cst major t fwd_arr queue back (forward_one a (mst 'md 'mb) cs addr) **
          R.pts_to oom_ref oom' ** pure ('oom == true ==> oom' == true)
{
  Sim.sim_facts a (mst 'md 'mb) g0 cs;
  minor_objects_valid (mst 'md 'mb) addr;
  minor_objects_body_bound (mst 'md 'mb) addr;
  minor_objects_not_infix (mst 'md 'mb) addr;
  Sim.sim_strict_room a (mst 'md 'mb) g0 cs addr;
  unfold cst;
  with g st farr q bk. assert (is_heap major g ** pages_st t st ** pts_to fwd_arr farr ** pts_to queue q **
                               R.pts_to back bk ** pure (Sim.matches cs g st farr q (SZ.v bk)));
  Sim.matches_elim cs g st farr q (SZ.v bk);
  let o = promote_one minor major t marking addr wz #a #ph #st;
  with g' st'. assert (is_heap major g' ** pages_st t st');
  if (U64.eq o 0UL) {
    Sim.step_normal_oom a (mst 'md 'mb) cs g st addr g' st';
    oom_ref := true;
    fold (cst major t fwd_arr queue back (forward_one a (mst 'md 'mb) cs addr))
  } else {
    Sim.step_normal_ok a (mst 'md 'mb) cs g st farr q (SZ.v bk) addr g' st' o;
    fwd_arr.(SZ.uint64_to_sizet (U64.div addr 8UL)) <- o;
    let b = !back;
    fits_queue (SZ.v b + 1);
    queue.(b) <- addr;
    back := SZ.add b 1sz;
    fold (cst major t fwd_arr queue back (forward_one a (mst 'md 'mb) cs addr))
  }
}
#pop-options

/// An infix address whose closure `p` is forwarded, to `pf`: the same
/// offset in the copy.
#push-options "--z3rlimit 30"
fn fwd_infix_done (major: heap_t) (t: pstate_t) (fwd_arr queue: array U64.t) (back: R.ref SZ.t)
  (addr p pf: U64.t)
  (#a: erased (tal pstate)) (#ms: erased minor_state) (#g0: erased heap) (#cs: erased (gstate pstate))
  requires cst major t fwd_arr queue back cs **
           pure (Sim.sim a ms g0 cs /\ cs.fwd addr == 0UL /\ is_infix_in_minor ms addr /\
                 p == infix_parent ms addr /\ pf == cs.fwd p /\ pf <> 0UL)
  ensures cst major t fwd_arr queue back (forward_one a ms cs addr)
{
  unfold cst;
  with g st farr q bk. assert (is_heap major g ** pages_st t st ** pts_to fwd_arr farr ** pts_to queue q ** R.pts_to back bk ** pure (Sim.matches cs g st farr q (SZ.v bk)));
  Sim.step_infix_fwd a ms g0 cs g st farr q (SZ.v bk) addr;
  let v = U64.add pf (U64.sub addr p);
  fwd_arr.(SZ.uint64_to_sizet (U64.div addr 8UL)) <- v;
  fold (cst major t fwd_arr queue back (forward_one a ms cs addr))
}
#pop-options

/// An infix address whose closure `p` is not forwarded: promote the
/// closure, record and queue it, and the address at the same offset.
#push-options "--z3rlimit 30"
fn fwd_infix_new (minor: minor_heap_t) (major: heap_t) (t: pstate_t) (marking: bool)
  (fwd_arr queue: array U64.t) (back: R.ref SZ.t) (oom_ref: R.ref bool) (addr p: U64.t)
  (#a: erased (tal pstate)) (#ph: erased I.phase) (#g0: erased heap) (#cs: erased (gstate pstate))
  requires is_minor minor 'md 'mb ** cst major t fwd_arr queue back cs ** R.pts_to oom_ref 'oom **
           pure (pre a ph marking (mst 'md 'mb) g0 cs /\
                 cs.fwd addr == 0UL /\ is_infix_in_minor (mst 'md 'mb) addr /\
                 p == infix_parent (mst 'md 'mb) addr /\ cs.fwd p == 0UL)
  ensures exists* oom'. is_minor minor 'md 'mb **
          cst major t fwd_arr queue back (forward_one a (mst 'md 'mb) cs addr) **
          R.pts_to oom_ref oom' ** pure ('oom == true ==> oom' == true)
{
  Sim.sim_facts a (mst 'md 'mb) g0 cs;
  infix_parent_in_minor_objects (mst 'md 'mb) addr;
  minor_objects_valid (mst 'md 'mb) p;
  minor_objects_body_bound (mst 'md 'mb) p;
  minor_objects_not_infix (mst 'md 'mb) p;
  Sim.sim_strict_room a (mst 'md 'mb) g0 cs p;
  let wz = read_minor_wosize minor p;
  unfold cst;
  with g st farr q bk. assert (is_heap major g ** pages_st t st ** pts_to fwd_arr farr ** pts_to queue q **
                               R.pts_to back bk ** pure (Sim.matches cs g st farr q (SZ.v bk)));
  Sim.matches_elim cs g st farr q (SZ.v bk);
  let o = promote_one minor major t marking p wz #a #ph #st;
  with g' st'. assert (is_heap major g' ** pages_st t st');
  if (U64.eq o 0UL) {
    Sim.step_infix_oom a (mst 'md 'mb) g0 cs g st addr g' st';
    oom_ref := true;
    fold (cst major t fwd_arr queue back (forward_one a (mst 'md 'mb) cs addr))
  } else {
    Sim.step_infix_new a (mst 'md 'mb) g0 cs g st farr q (SZ.v bk) addr g' st' o;
    fwd_arr.(SZ.uint64_to_sizet (U64.div p 8UL)) <- o;
    let b = !back;
    fits_queue (SZ.v b + 1);
    queue.(b) <- p;
    back := SZ.add b 1sz;
    let v = U64.add o (U64.sub addr p);
    fwd_arr.(SZ.uint64_to_sizet (U64.div addr 8UL)) <- v;
    fold (cst major t fwd_arr queue back (forward_one a (mst 'md 'mb) cs addr))
  }
}
#pop-options

/// Nothing to do: the state is the step's.
ghost
fn skip (major: heap_t) (t: pstate_t) (fwd_arr queue: array U64.t) (back: R.ref SZ.t) (addr: U64.t)
  (#a: erased (tal pstate)) (#ms: erased minor_state) (#cs: erased (gstate pstate))
  requires cst major t fwd_arr queue back cs **
           pure (cs.fwd addr <> 0UL \/ (~(is_infix_in_minor ms addr) /\ ~(Seq.mem addr (minor_objects ms))))
  ensures cst major t fwd_arr queue back (forward_one a ms cs addr)
{
  Sim.step_skip a ms cs addr;
  rewrite (cst major t fwd_arr queue back cs) as (cst major t fwd_arr queue back (forward_one a ms cs addr))
}

/// An infix address: through its closure.
#push-options "--z3rlimit 30"
fn fwd_infix (minor: minor_heap_t) (major: heap_t) (t: pstate_t) (marking: bool)
  (fwd_arr queue: array U64.t) (back: R.ref SZ.t) (oom_ref: R.ref bool) (addr: U64.t)
  (#a: erased (tal pstate)) (#ph: erased I.phase) (#g0: erased heap) (#cs: erased (gstate pstate))
  requires is_minor minor 'md 'mb ** cst major t fwd_arr queue back cs ** R.pts_to oom_ref 'oom **
           pure (pre a ph marking (mst 'md 'mb) g0 cs /\
                 cs.fwd addr == 0UL /\ is_infix_in_minor (mst 'md 'mb) addr)
  ensures exists* oom'. is_minor minor 'md 'mb **
          cst major t fwd_arr queue back (forward_one a (mst 'md 'mb) cs addr) **
          R.pts_to oom_ref oom' ** pure ('oom == true ==> oom' == true)
{
  Sim.sim_facts a (mst 'md 'mb) g0 cs;
  infix_parent_value (mst 'md 'mb) addr;
  infix_parent_in_minor_objects (mst 'md 'mb) addr;
  let wz = read_minor_wosize minor addr;
  let p = U64.sub addr (U64.mul wz 8UL);
  let pf = get_fwd major t fwd_arr queue back p;
  if (U64.eq pf 0UL) {
    fwd_infix_new minor major t marking fwd_arr queue back oom_ref addr p #a #ph #g0 #cs
  } else {
    fwd_infix_done major t fwd_arr queue back addr p pf #a #(mst 'md 'mb) #g0 #cs
  }
}
#pop-options

/// **Forward `addr`**: exactly the model's `forward_one`.
#push-options "--z3rlimit 30"
fn forward_if_minor (minor: minor_heap_t) (major: heap_t) (t: pstate_t) (marking: bool)
  (fwd_arr queue: array U64.t) (back: R.ref SZ.t) (oom_ref: R.ref bool) (addr: U64.t)
  (#a: erased (tal pstate)) (#ph: erased I.phase) (#g0: erased heap) (#cs: erased (gstate pstate))
  requires is_minor minor 'md 'mb ** cst major t fwd_arr queue back cs ** R.pts_to oom_ref 'oom **
           pure (pre a ph marking (mst 'md 'mb) g0 cs)
  ensures exists* oom'. is_minor minor 'md 'mb **
          cst major t fwd_arr queue back (forward_one a (mst 'md 'mb) cs addr) **
          R.pts_to oom_ref oom' **
          pure ('oom == true ==> oom' == true) **
          pure (pre a ph marking (mst 'md 'mb) g0 (forward_one a (mst 'md 'mb) cs addr))
{
  Sim.sim_forward_one a (mst 'md 'mb) g0 cs addr;
  Sim.sim_facts a (mst 'md 'mb) g0 cs;
  if (U64.lt addr 8UL || U64.gte addr minor_heap_size_u64 || U64.rem addr 8UL <> 0UL) {
    CSim.not_minor_if_guards_fail (mst 'md 'mb) addr;
    skip major t fwd_arr queue back addr #a #(mst 'md 'mb) #cs
  } else {
    let f = get_fwd major t fwd_arr queue back addr;
    if (f <> 0UL) {
      skip major t fwd_arr queue back addr #a #(mst 'md 'mb) #cs
    } else {
      let tag = read_minor_tag minor addr;
      if (U64.eq tag 249UL) {
        fwd_infix minor major t marking fwd_arr queue back oom_ref addr #a #ph #g0 #cs
      } else {
        let wz = read_minor_wosize minor addr;
        if (U64.eq wz 0UL || U64.gte wz minor_heap_size_u64) {
          FStar.Classical.move_requires (minor_objects_body_bound (mst 'md 'mb)) addr;
          skip major t fwd_arr queue back addr #a #(mst 'md 'mb) #cs
        } else {
          minor_arith_no_overflow (U64.v addr) (U64.v wz);
          if (U64.gt (U64.add addr (U64.mul wz 8UL)) minor_heap_size_u64) {
            CSim.not_minor_if_wosize_bounds_fail (mst 'md 'mb) addr;
            skip major t fwd_arr queue back addr #a #(mst 'md 'mb) #cs
          } else {
            CSim.minor_guards_sufficient (mst 'md 'mb) addr;
            fwd_normal minor major t marking fwd_arr queue back oom_ref addr wz #a #ph #g0 #cs
          }
        }
      }
    }
  }
}
#pop-options
