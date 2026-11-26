/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Simulation.Minor - the simulation across a minor collection
/// ---------------------------------------------------------------------------
///
/// A minor collection keeps the joint invariant of `GC.Gen.Run.Simulation`
/// (stated on its parts; that module calls this one).  The map from blocks
/// to objects follows the forwarding map: a promoted copy holds its
/// original's object, a nursery block that was not promoted drops out, and
/// the major blocks keep theirs.  Every object the program can reach is
/// kept: its nursery block, if any, is promoted -- reachable from the roots
/// or from a remembered slot, through nursery blocks that are promoted, whose
/// fields Cheney forwards (`GC.Gen.CheneyBFS.cheney_no_oom`).  The copies are
/// faithful: a field that held a nursery pointer now points at the target's
/// copy (at the same offset, for an infix pointer), and every other word is
/// unchanged -- a `Word` never looks like a nursery pointer
/// (`GC.Model.Represents.outside_heaps`).

module GC.Gen.Run.Simulation.Minor

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant
open GC.Model.Represents

module U64 = FStar.UInt64
module I = GC.Model.Ideal

/// **A minor collection keeps the joint invariant** (`sim_inv`, spelled out).
val minor_keeps (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (roots: seq U64.t) (r': real_state)
  : Lemma (requires run_invariant r h /\ represents r h im ids /\ I.wf_memory im /\ I.wf_objects im /\
                    (forall (x: obj_addr) (id: I.obj_id). ids (Major x) == Some id /\ I.reachable im id ==> kept h x) /\
                    roots_represented ids (ptr_values im.I.roots) roots /\ step r (Minor roots) r')
          (ensures (let h' = update_history h r (Minor roots) r' in
                    let ids' = update_block_ids ids (Seq.length im.I.objects) r (Minor roots) r' in
                    run_invariant r' h' /\ represents r' h' im ids' /\
                    (forall (x: obj_addr) (id: I.obj_id).
                       ids' (Major x) == Some id /\ I.reachable im id ==> kept h' x)))
