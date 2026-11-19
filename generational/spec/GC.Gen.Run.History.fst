/// ---------------------------------------------------------------------------
/// GC.Gen.Run.History - the major cycle's history along a run
/// ---------------------------------------------------------------------------
///
/// What the snapshot-at-the-beginning accounting is relative to
/// (mutator-equivalence-plan.md, section 3.3): the memory and the roots at
/// the last `start_cycle`, and the major-heap blocks allocated since --
/// directly or by promotion (a promotion is an allocation).  It is a ghost
/// function of the run (`update_history`, `history_along`), not part of the
/// step, so `step` stays what the Pulse contracts describe.
///
/// From it, four sets of major-heap addresses (all fixed by the history):
///   * `snapshot`: the objects reachable from the start roots in the start
///     memory;
///   * `allocated_during_cycle`: blocks allocated since;
///   * `free_at_start`: the free (blue) blocks of the start memory;
///   * `garbage_at_start`: the allocated blocks of the start memory not in the
///     snapshot -- what the cycle exists to collect.
///
/// Before any cycle the history is that of a cycle started at time 0 on the
/// initial memory (nothing allocated, every block free) with no roots, so
/// the invariant's clauses need no special case.

module GC.Gen.Run.History

open FStar.Seq
open FStar.List.Tot
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Run.Step

module U64 = FStar.UInt64
module GMC = GC.Gen.MarkPhase.Completeness
module SPC = GC.Spec.SweepPhase.Completeness
module LL = GC.Spec.FusedSweep.Lossless

/// **The cycle's history**: the memory and roots `start_cycle` was called
/// with, and the major-heap blocks allocated since.
noeq type cycle_history = {
  start_memory: real_memory;
  start_roots: seq U64.t;
  allocated_during_cycle: obj_addr -> prop;
}

/// **The snapshot**: what the start roots reached in the start memory (the
/// nursery is empty at a `start_cycle`).
let snapshot (h: cycle_history) (x: obj_addr) : prop =
  GMC.reachable_at_start h.start_memory.major h.start_roots x

/// The free (blue) blocks of the start memory.
let free_at_start (h: cycle_history) (x: obj_addr) : prop =
  Seq.mem x (objects zero_addr h.start_memory.major) /\ is_blue x h.start_memory.major

/// The allocated blocks of the start memory outside the snapshot.
let garbage_at_start (h: cycle_history) (x: obj_addr) : prop =
  is_allocated h.start_memory (Major x) /\ ~(snapshot h x)

/// The snapshot and what was allocated since.
let kept (h: cycle_history) (x: obj_addr) : prop =
  snapshot h x \/ h.allocated_during_cycle x

/// The word `p` was in a free block, or a garbage block, of the start
/// memory: space the cycle may hand out again.
let reclaimable_at_start (h: cycle_history) (p: nat) : prop =
  exists (y: obj_addr). Seq.mem y (objects zero_addr h.start_memory.major) /\
    (free_at_start h y \/ garbage_at_start h y) /\ LL.in_extent h.start_memory.major y p

/// The major blocks a step made allocated: an allocation's new block, a
/// minor collection's promoted copies.
let made (r r': real_state) (x: obj_addr) : prop =
  is_allocated r'.memory (Major x) /\ ~(is_allocated r.memory (Major x))

/// **The history after a step.**
let update_history (h: cycle_history) (r: real_state) (e: event) (r': real_state) : cycle_history =
  match e with
  | StartCycle roots ->
      { start_memory = r.memory; start_roots = roots; allocated_during_cycle = SPC.nothing_new }
  | Alloc _ _ _ _
  | Minor _ ->
      { h with allocated_during_cycle = (fun x -> h.allocated_during_cycle x \/ made r r' x) }
  | _ -> h

/// The history before any cycle.
let initial_history (_: unit) : GTot cycle_history =
  { start_memory = (initial_state ()).memory; start_roots = Seq.empty;
    allocated_during_cycle = SPC.nothing_new }

/// The history along a run, from `h0`.
let rec history_along (h0: cycle_history) (#r0: real_state) (#es: list event) (#r1: real_state)
                      (rn: run r0 es r1)
  : GTot cycle_history (decreases rn) =
  match rn with
  | Done _ -> h0
  | Step #_ #_ #r1' rn' e r2 _ -> update_history (history_along h0 rn') r1' e r2

/// The history of a run from the initial state.
let history_of_run (#es: list event) (#r: real_state) (rn: run (initial_state ()) es r)
  : GTot cycle_history =
  history_along (initial_history ()) rn
