/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Invariant.Defs - the run invariant's definitions
/// ---------------------------------------------------------------------------
///
/// The definitions of `GC.Gen.Run.Invariant` (which includes this module and
/// documents them), in a module of their own so that the modules proving its
/// lemmas can depend on them without a cycle.

module GC.Gen.Run.Invariant.Defs

open FStar.Seq
open FStar.List.Tot
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module MP = GC.Spec.MarkPhase
module MPC = GC.Spec.MarkPhase.Completeness
module SPC = GC.Spec.SweepPhase.Completeness
module SA = GC.Spec.Allocator
module AC = GC.Spec.Allocator.Cursor
module LL = GC.Spec.FusedSweep.Lossless
module W = GC.Spec.Walk
module GI = GC.Gen.Incremental
module RT = GC.Gen.RefTable
module GenInv = GC.Gen.HeapInvariant
module GBase = GC.Gen.Base
module I = GC.Model.Ideal

/// ---------------------------------------------------------------------------
/// The invariant
/// ---------------------------------------------------------------------------

/// **The nursery's pointers name nursery objects**: a scanned field of a
/// nursery object that is a nursery pointer resolves to a nursery object
/// (what `storable_value` asks of every young value the program stores).
let nursery_fields_valid (ms: minor_state) : prop =
  forall (o: U64.t) (j: nat).
    Seq.mem o (minor_objects ms) /\ j < minor_scan_wosize ms o /\ is_young (minor_read_field ms o j) ==>
    Seq.mem (resolve_minor ms (GBase.to_minor_offset (minor_read_field ms o j))) (minor_objects ms)

/// **The shape of the real state**, at its phase.
let phase_shape (r: real_state) : prop =
  let g = r.memory.major in
  let free = GI.phase_free r.phase in
  GI.phase_shape r.memory.nursery g r.free_list r.phase r.scan_pos /\
  RT.ref_table_covers_with free g r.ref_table (Seq.length r.ref_table) /\
  RT.ref_table_sound_with free g r.ref_table (Seq.length r.ref_table) /\
  W.walk_end g zero_addr + 8 >= heap_size /\
  nursery_fields_valid r.memory.nursery /\
  // with the nursery empty, so is the remembered set
  (minor_objects r.memory.nursery == Seq.empty ==> Seq.length r.ref_table == 0)

/// **The snapshot accounting** (B1-B5, and the phase's additions).
let snapshot_accounting (r: real_state) (h: cycle_history) : prop =
  let g = r.memory.major in
  let g0 = h.start_memory.major in
  // B1
  MPC.within_snapshot (kept h) g /\
  GenInv.minor_major_fields_not_free (MPC.outside_snapshot (kept h)) r.memory.nursery g /\
  (forall (i: nat). i < Seq.length r.ref_table ==>
     (exists (x: obj_addr) (j: nat). kept h x /\ j < U64.v (wosize_of_object x g) /\
        U64.v (Seq.index r.ref_table i) == U64.v x + j * 8)) /\
  // B2
  (forall (x: obj_addr). snapshot h x ==>
     Seq.mem x (objects zero_addr g) /\ ~(is_blue x g) /\ wosize_of_object x g == wosize_of_object x g0) /\
  (forall (x: obj_addr). snapshot h x ==> is_allocated h.start_memory (Major x)) /\
  (forall (x: obj_addr). garbage_at_start h x /\ is_allocated r.memory (Major x) /\ ~(h.allocated_during_cycle x) ==>
     wosize_of_object x g == wosize_of_object x g0) /\
  W.walk_end g zero_addr == W.walk_end g0 zero_addr /\
  // B3
  (forall (x: obj_addr). h.allocated_during_cycle x ==> is_allocated r.memory (Major x) /\ ~(snapshot h x)) /\
  // B4
  (forall (x: obj_addr). is_allocated r.memory (Major x) ==>
     snapshot h x \/ h.allocated_during_cycle x \/ garbage_at_start h x) /\
  // B5
  (forall (p: nat). LL.blue_covered g p \/ SPC.new_covered h.allocated_during_cycle g p ==>
     reclaimable_at_start h p) /\
  (match r.phase with
   | Ph.Marking ->
       MP.outside_refs_reached g r.scan_pos (snapshot h) /\
       (forall (x: obj_addr). h.allocated_during_cycle x ==> is_black x g)
   | Ph.Sweeping c ->
       MPC.sweep_in_snapshot (kept h) g c /\
       (forall (x: obj_addr). kept h x /\ U64.v x > U64.v c ==> is_black x g)
   | Ph.Idle -> forall (x: obj_addr). is_allocated r.memory (Major x) ==> kept h x)

/// **The run invariant.**
let run_invariant (r: real_state) (h: cycle_history) : prop =
  phase_shape r /\ snapshot_accounting r h
