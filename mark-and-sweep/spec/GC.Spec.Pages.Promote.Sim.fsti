/// ---------------------------------------------------------------------------
/// GC.Spec.Pages.Promote.Sim - the Pulse promotion's loop, against the model
/// ---------------------------------------------------------------------------
///
/// Plan §30.  What the Pulse minor collection (`GC.Impl.Pages.Promote`,
/// `GC.Impl.Pages.Cheney`, `GC.Impl.Pages.Minor`) needs of the model's
/// promotion (`GC.Spec.Pages.Promote`), stated so that its proofs see no
/// definition of the loop:
///
///   * `at_phase a ph`: the allocator `a` is the page allocator of phase
///     `ph` (`AllocTag.alloc_tag ph`, which `AllocInc.alloc_ph` computes),
///     its invariant gives the phase's (`Incr.phase_inv`), and it meets the
///     promotion's contract.  The instances: `Marking`, `Sweeping`, `Idle`;
///   * `sim a minor g0 cs`: the loop invariant, abstract.  It is the model's
///     `Loop.linv`, the queue's facts (akhil's `Cheney.SimOne.cheney_bfs_inv`
///     over our state), and that forwarding is injective on nursery objects
///     (two copies are two blocks), which the pointer update needs
///     (`TwoPass`).  Every step of the loop keeps it (`sim_forward_one`);
///   * `matches cs g st farr q bk`: the Pulse state is the model state `cs`
///     (akhil's `Cheney.Sim.impl_matches_spec`, with the allocator's state
///     in place of his free-list head), abstract;
///   * one lemma per branch of the Pulse forwarding step: the state it
///     leaves matches `forward_one`.

module GC.Spec.Pages.Promote.Sim

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.ForwardingArray
open GC.Spec.Pages.Map
open GC.Spec.Pages.Inv
open GC.Spec.Pages.Promote

module U64 = FStar.UInt64
module I = GC.Spec.AllocIface
module AT = GC.Spec.Pages.AllocTag
module Inc = GC.Spec.Pages.Incr
module L = GC.Spec.Pages.Promote.Loop
module MS = GC.Spec.Pages.MidSweep
module FW = GC.Spec.Pages.Promote.Follow

#set-options "--fuel 0 --ifuel 0 --z3rlimit 20"

/// ---------------------------------------------------------------------------
/// The allocator of a phase
/// ---------------------------------------------------------------------------

val at_phase (a: tal pstate) (ph: I.phase) : prop

val at_phase_alloc (a: tal pstate) (ph: I.phase) (g: heap) (st: pstate) (wz: nat) (tag: AT.tag_t)
  : Lemma (requires at_phase a ph)
          (ensures a.alloc g st wz tag == AT.alloc_tag ph g st wz tag)

val at_phase_inv (a: tal pstate) (ph: I.phase) (g: heap) (st: pstate)
  : Lemma (requires at_phase a ph /\ a.inv g st)
          (ensures Inc.phase_inv ph g st)

val at_phase_contract (a: tal pstate) (ph: I.phase)
  : Lemma (requires at_phase a ph) (ensures contract a)

/// An allocation from the invariant: nothing, or a block with room.
val alloc_room (a: tal pstate) (g: heap) (st: pstate) (wz: pos) (tag: AT.tag_t)
  : Lemma (requires contract a /\ a.inv g st /\ U64.v tag <> 249)
          (ensures (let (g', st', o) = a.alloc g st wz tag in
                    (o == 0UL ==> g' == g /\ st' == st) /\
                    (o <> 0UL ==> U64.v o >= 8 /\ U64.v o < heap_size /\ U64.v o % 8 == 0 /\
                                  U64.v o + wz * 8 <= heap_size)))

/// **The instances**: the page allocator while marking, mid-sweep (free as
/// at the page map `pm0`), and idle.
val mark_at (_: unit) : Lemma (at_phase GC.Spec.Pages.PromoteInst.mark_tal I.Marking)
val sw_at (pm0: page_map) : Lemma (at_phase (GC.Spec.Pages.PromoteInst.sw_tal pm0) I.Sweeping)
val idle_at (_: unit) : Lemma (at_phase GC.Spec.Pages.Promote.Idle.idle_tal I.Idle)

/// ---------------------------------------------------------------------------
/// The loop invariant
/// ---------------------------------------------------------------------------

/// The loop's first state.
let init (g0: heap) (st0: pstate) : gstate pstate =
  { major = g0; st = st0; fwd = empty_forwarding; queue = Seq.empty }

/// Forwarding is injective on nursery objects: two copies are two blocks.
let fwd_injective (minor: minor_state) (fwd: forwarding_map) : prop =
  forall (m1 m2: U64.t).
    fwd m1 <> 0UL /\ fwd m2 <> 0UL /\ fwd m1 == fwd m2 /\
    ~(is_infix_in_minor minor m1) /\ ~(is_infix_in_minor minor m2) ==> m1 == m2

val sim (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) : prop

val sim_init (a: tal pstate) (minor: minor_state) (g0: heap) (st0: pstate) (roots: seq U64.t)
  : Lemma (requires L.cpre_w a minor g0 st0 roots)
          (ensures sim a minor g0 (init g0 st0))

/// What the Pulse loop reads off the invariant.
val sim_facts (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate)
  : Lemma (requires sim a minor g0 cs)
          (ensures minor_wf minor /\ FW.fields_follow minor /\ a.inv cs.major cs.st /\
                   contract a /\ Seq.length cs.queue <= Seq.length (minor_objects minor) /\
                   Seq.length (minor_objects minor) < fwd_array_size)

/// The queue holds nursery objects.
val sim_queue (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) (j: nat)
  : Lemma (requires sim a minor g0 cs /\ j < Seq.length cs.queue)
          (ensures Seq.mem (Seq.index cs.queue j) (minor_objects minor))

/// A forwarded nursery object's copy has room for its body.
val sim_room (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) (x: U64.t)
  : Lemma (requires sim a minor g0 cs /\ Seq.mem x (minor_objects minor) /\ cs.fwd x <> 0UL)
          (ensures U64.v (cs.fwd x) >= 8 /\ U64.v (cs.fwd x) % 8 == 0 /\
                   U64.v (cs.fwd x) + minor_wosize minor x * 8 <= heap_size)

/// A nursery object not yet forwarded leaves room in the queue.
val sim_strict_room (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) (x: U64.t)
  : Lemma (requires sim a minor g0 cs /\ Seq.mem x (minor_objects minor) /\ cs.fwd x == 0UL)
          (ensures Seq.length cs.queue < Seq.length (minor_objects minor))

/// **Every step keeps the invariant.**
val sim_forward_one (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) (addr: U64.t)
  : Lemma (requires sim a minor g0 cs /\ FW.follow_ok minor addr)
          (ensures sim a minor g0 (forward_one a minor cs addr))

/// ---------------------------------------------------------------------------
/// The Pulse state and the model state
/// ---------------------------------------------------------------------------

val matches_core (cs: gstate pstate) (g: heap) (st: pstate) (farr q: seq U64.t) (bk: nat) : prop

let matches (cs: gstate pstate) (g: heap) (st: pstate) (farr q: seq U64.t) (bk: nat) : prop =
  Seq.length farr == fwd_array_size /\ Seq.length q == queue_size /\
  bk == Seq.length cs.queue /\ bk <= queue_size /\ matches_core cs g st farr q bk

val matches_elim (cs: gstate pstate) (g: heap) (st: pstate) (farr q: seq U64.t) (bk: nat)
  : Lemma (requires matches cs g st farr q bk)
          (ensures g == cs.major /\ st == cs.st /\ bk == Seq.length cs.queue /\ bk <= queue_size /\
                   Seq.length q == queue_size /\ Seq.length farr == fwd_array_size /\
                   represents_fwd farr cs.fwd)

val matches_init (g: heap) (st: pstate) (farr q: seq U64.t)
  : Lemma (requires Seq.length farr == fwd_array_size /\ Seq.length q == queue_size /\
                    (forall (i: nat). i < fwd_array_size ==> Seq.index farr i == 0UL))
          (ensures matches (init g st) g st farr q 0)

/// The forwarding array at a nursery address.
val matches_fwd (cs: gstate pstate) (g: heap) (st: pstate) (farr q: seq U64.t) (bk: nat) (addr: U64.t)
  : Lemma (requires matches cs g st farr q bk /\
                    U64.v addr >= 8 /\ U64.v addr < minor_heap_size /\ U64.v addr % 8 == 0)
          (ensures U64.v addr / 8 < fwd_array_size /\ Seq.index farr (U64.v addr / 8) == cs.fwd addr)

/// The queue array below the back.
val matches_queue (cs: gstate pstate) (g: heap) (st: pstate) (farr q: seq U64.t) (bk: nat) (j: nat)
  : Lemma (requires matches cs g st farr q bk /\ j < bk)
          (ensures Seq.index q j == Seq.index cs.queue j)

/// ---------------------------------------------------------------------------
/// The forwarding step, branch by branch
/// ---------------------------------------------------------------------------

/// Nothing to do: already forwarded, or not a nursery object nor an infix
/// address in one.
val step_skip (a: tal pstate) (minor: minor_state) (cs: gstate pstate) (addr: U64.t)
  : Lemma (requires cs.fwd addr <> 0UL \/
                    (~(is_infix_in_minor minor addr) /\ ~(Seq.mem addr (minor_objects minor))))
          (ensures forward_one a minor cs addr == cs)

/// A nursery object, promoted to `o`, recorded and queued.
val step_normal_ok (a: tal pstate) (minor: minor_state) (cs: gstate pstate)
                   (g: heap) (st: pstate) (farr q: seq U64.t) (bk: nat)
                   (addr: U64.t) (g': heap) (st': pstate) (o: U64.t)
  : Lemma (requires matches cs g st farr q bk /\ minor_wf minor /\
                    cs.fwd addr == 0UL /\ Seq.mem addr (minor_objects minor) /\
                    minor_wosize minor addr > 0 /\ bk < queue_size /\
                    promote_object a minor g addr st (minor_wosize minor addr) == (g', st', o) /\
                    o <> 0UL)
          (ensures U64.v addr / 8 < fwd_array_size /\
                   matches (forward_one a minor cs addr) g' st'
                     (Seq.upd farr (U64.v addr / 8) o) (Seq.upd q bk addr) (bk + 1))

/// A nursery object whose promotion failed: nothing changes.
val step_normal_oom (a: tal pstate) (minor: minor_state) (cs: gstate pstate) (g: heap) (st: pstate)
                    (addr: U64.t) (g': heap) (st': pstate)
  : Lemma (requires g == cs.major /\ st == cs.st /\ minor_wf minor /\
                    cs.fwd addr == 0UL /\ Seq.mem addr (minor_objects minor) /\
                    minor_wosize minor addr > 0 /\
                    promote_object a minor g addr st (minor_wosize minor addr) == (g', st', 0UL))
          (ensures forward_one a minor cs addr == cs /\ g' == g /\ st' == st)

/// An infix address whose closure is forwarded: the same offset in its copy.
val step_infix_fwd (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate)
                   (g: heap) (st: pstate) (farr q: seq U64.t) (bk: nat) (addr: U64.t)
  : Lemma (requires matches cs g st farr q bk /\ sim a minor g0 cs /\ FW.follow_ok minor addr /\
                    cs.fwd addr == 0UL /\ is_infix_in_minor minor addr /\
                    cs.fwd (infix_parent minor addr) <> 0UL)
          (ensures (let p = infix_parent minor addr in
                    let v = U64.v (cs.fwd p) + (U64.v addr - U64.v p) in
                    U64.v addr >= U64.v p /\ v < heap_size /\ U64.v addr / 8 < fwd_array_size /\
                    matches (forward_one a minor cs addr) g st
                      (Seq.upd farr (U64.v addr / 8) (U64.uint_to_t v)) q bk))

/// An infix address whose closure is promoted now, to `o`: the closure
/// recorded and queued, the address at the same offset in the copy.
val step_infix_new (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate)
                   (g: heap) (st: pstate) (farr q: seq U64.t) (bk: nat)
                   (addr: U64.t) (g': heap) (st': pstate) (o: U64.t)
  : Lemma (requires matches cs g st farr q bk /\ sim a minor g0 cs /\ FW.follow_ok minor addr /\
                    cs.fwd addr == 0UL /\ is_infix_in_minor minor addr /\
                    (let p = infix_parent minor addr in
                     U64.v p >= 8 /\ U64.v p < minor_heap_size /\ U64.v p % 8 == 0 /\
                     minor_wosize minor p > 0 /\ cs.fwd p == 0UL /\ bk < queue_size /\
                     promote_object a minor g p st (minor_wosize minor p) == (g', st', o) /\
                     o <> 0UL))
          (ensures (let p = infix_parent minor addr in
                    let v = U64.v o + (U64.v addr - U64.v p) in
                    U64.v addr >= U64.v p /\ v < heap_size /\
                    U64.v p / 8 < fwd_array_size /\ U64.v addr / 8 < fwd_array_size /\
                    matches (forward_one a minor cs addr) g' st'
                      (Seq.upd (Seq.upd farr (U64.v p / 8) o) (U64.v addr / 8) (U64.uint_to_t v))
                      (Seq.upd q bk p) (bk + 1)))

/// An infix address whose closure's promotion failed: nothing changes.
val step_infix_oom (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate)
                   (g: heap) (st: pstate) (addr: U64.t) (g': heap) (st': pstate)
  : Lemma (requires g == cs.major /\ st == cs.st /\ sim a minor g0 cs /\ FW.follow_ok minor addr /\
                    cs.fwd addr == 0UL /\ is_infix_in_minor minor addr /\
                    (let p = infix_parent minor addr in
                     minor_wosize minor p > 0 /\ cs.fwd p == 0UL /\
                     promote_object a minor g p st (minor_wosize minor p) == (g', st', 0UL)))
          (ensures forward_one a minor cs addr == cs /\ g' == g /\ st' == st)

/// ---------------------------------------------------------------------------
/// The loops, a step at a time
/// ---------------------------------------------------------------------------

val fields_step (a: tal pstate) (minor: minor_state) (cs: gstate pstate) (p: U64.t) (i wz: nat)
  : Lemma (requires i < wz)
          (ensures forward_fields a minor cs p i wz ==
                   forward_fields a minor (forward_one a minor cs (to_minor_offset (minor_read_field minor p i)))
                     p (i + 1) wz)

val fields_base (a: tal pstate) (minor: minor_state) (cs: gstate pstate) (p: U64.t) (i wz: nat)
  : Lemma (requires i >= wz) (ensures forward_fields a minor cs p i wz == cs)

val roots_step (a: tal pstate) (minor: minor_state) (cs: gstate pstate) (roots: seq U64.t) (i: nat)
  : Lemma (requires i < Seq.length roots)
          (ensures forward_roots a minor cs roots i ==
                   forward_roots a minor (forward_one a minor cs (Seq.index roots i)) roots (i + 1))

val roots_base (a: tal pstate) (minor: minor_state) (cs: gstate pstate) (roots: seq U64.t) (i: nat)
  : Lemma (requires i >= Seq.length roots) (ensures forward_roots a minor cs roots i == cs)

val scan_step (a: tal pstate) (minor: minor_state) (cs: gstate pstate) (sc fuel: nat)
  : Lemma (requires fuel > 0 /\ sc < Seq.length cs.queue)
          (ensures scan a minor cs sc fuel ==
                   scan a minor
                     (forward_fields a minor cs (Seq.index cs.queue sc) 0
                        (minor_scan_wosize minor (Seq.index cs.queue sc)))
                     (sc + 1) (fuel - 1))

val scan_base (a: tal pstate) (minor: minor_state) (cs: gstate pstate) (sc fuel: nat)
  : Lemma (requires sc >= Seq.length cs.queue) (ensures scan a minor cs sc fuel == cs)

/// The fields loop keeps the invariant.
val sim_fields (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate) (p: U64.t) (i wz: nat)
  : Lemma (requires sim a minor g0 cs /\ Seq.mem p (minor_objects minor) /\ wz <= minor_scan_wosize minor p)
          (ensures sim a minor g0 (forward_fields a minor cs p i wz))

/// **Promotion ends in the invariant.**
val promote_sim (a: tal pstate) (minor: minor_state) (g0: heap) (st0: pstate) (roots: seq U64.t)
  : Lemma (requires L.cpre_w a minor g0 st0 roots)
          (ensures sim a minor g0 (promote a minor g0 st0 roots))

/// What the invariant gives at the end, for the pointer update.
val sim_end (a: tal pstate) (minor: minor_state) (g0: heap) (cs: gstate pstate)
  : Lemma (requires sim a minor g0 cs)
          (ensures L.ctx_w a minor g0 /\ L.linv a minor g0 cs /\ L.finv minor cs /\ fwd_injective minor cs.fwd)
