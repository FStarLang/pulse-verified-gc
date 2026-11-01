/// ---------------------------------------------------------------------------
/// GC.Spec.MarkPar — parallel mark by ownership: model and statement
///
/// The heap is cut into k address ranges.  Range i is worker i's.  An object
/// belongs to the range holding its header; an interior (infix) pointer is
/// first resolved to its parent closure.  Each worker has its own work list
/// and its own inbox, and writes the colour only of objects it owns:
///
///   Pop i      worker i pops x from its work list and blackens it; it then
///              scans x's fields one at a time (unless x is no-scan or has
///              no fields)
///   Scan i     worker i looks at the next field of the object it is
///              scanning.  A pointer is resolved to the object `c` it names.
///              If i owns c and c is white, i greys it and pushes it.  If
///              another range owns c, i sends c's address to that range.
///   Take i     worker i takes the first address in its inbox, and greys
///              and pushes it if it is white
///   Deliver j  the j-th message in transit reaches its range's inbox
///
/// Messages in transit are a list, and any of them may be delivered next, so
/// delivery may reorder messages.  Each root starts in its owner's inbox.
/// A run is a schedule: any list of events.  An event that is not enabled
/// (popping an empty work list, say) changes nothing, so every list is a
/// schedule and every interleaving is some list.  Marking has ended when
/// every work list, every inbox and the network are empty and no worker is
/// part-way through an object (`quiescent`).
///
/// The theorem, `mark_par_correct`: for every cut list and every schedule,
/// if the run has ended, its heap is the sequential mark's, byte for byte.
/// ---------------------------------------------------------------------------
module GC.Spec.MarkPar

open FStar.Seq
module U64 = FStar.UInt64
module Seq = FStar.Seq
module L = FStar.List.Tot

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Spec.DFS
open GC.Spec.MarkPar.Exec

module HeapGraph = GC.Spec.HeapGraph
module Mark = GC.Spec.Mark

include GC.Spec.MarkPar.Model


/// ---------------------------------------------------------------------------
/// The statements
/// ---------------------------------------------------------------------------

/// For every cut list and every schedule, a run that has ended leaves the
/// heap the sequential mark leaves, byte for byte.
val mark_par_correct (cs: list nat) (g: heap) (roots: list obj_addr) (sched: list event)
  : Lemma (requires mark_pre g roots /\ valid_cuts cs /\
                    quiescent (run cs g roots sched))
          (ensures (run cs g roots sched).heap == sequential_mark g roots)

let mark_par_correct cs g roots sched = admit ()

/// The same conclusion said without the sequential mark: exactly the objects
/// reachable from the roots are black, each is the original header made
/// black, and every other word of the heap is unchanged.  The graph
/// hypotheses are `end_to_end_correctness`'s.
val mark_par_reachable (cs: list nat) (g: heap) (roots: list obj_addr) (sched: list event)
  : Lemma (requires mark_pre g roots /\ valid_cuts cs /\
                    quiescent (run cs g roots sched) /\
                    graph_pre g roots)
          (ensures (let h = (run cs g roots sched).heap in
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                       (is_black x h <==> reachable g roots x)) /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ reachable g roots x ==>
                       read_word h (hd_address x) == read_word (makeBlack x g) (hd_address x)) /\
                    (forall (a: hp_addr).
                       (forall (x: obj_addr). Seq.mem x (objects zero_addr g) /\ reachable g roots x ==>
                          a <> hd_address x) ==>
                       read_word h a == read_word g a)))

let mark_par_reachable cs g roots sched = admit ()

/// Only the owner writes a colour: from any state a run reaches, the next
/// step changes the heap only in the header of an enumerated object that the
/// acting worker owns.
val step_writes_own (cs: list nat) (g: heap) (roots: list obj_addr) (sched: list event)
    (e: event) (a: hp_addr)
  : Lemma (requires mark_pre g roots /\ valid_cuts cs /\
                    (let s = run cs g roots sched in
                     read_word (step cs s e).heap a <> read_word s.heap a))
          (ensures exists (x: obj_addr).
                     a == hd_address x /\ Seq.mem x (objects zero_addr g) /\
                     owner cs x == actor e)

let step_writes_own cs g roots sched e a = admit ()

/// Every run ends: a schedule has at most `measure (init ...)` effective
/// steps, a step that is not enabled changes nothing, and a run that has
/// not ended always has an enabled step.  So any schedule that keeps taking
/// enabled steps reaches `quiescent` within that many.  The bound is at
/// most 3 * heap_words plus the number of roots.
val mark_par_terminates (cs: list nat) (g: heap) (roots: list obj_addr) (sched: list event)
  : Lemma (requires mark_pre g roots /\ valid_cuts cs)
          (ensures (let s = run cs g roots sched in
                    effective_steps cs (init cs g roots) sched <= measure (init cs g roots) /\
                    (forall (e: event). ~(L.mem e (enabled s)) ==> step cs s e == s) /\
                    (enabled s == [] <==> quiescent s)))

let mark_par_terminates cs g roots sched = admit ()
