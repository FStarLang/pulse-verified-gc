/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Simulation.Collector - the simulation across collector steps
/// ---------------------------------------------------------------------------
///
/// The collector's half of `GC.Gen.Run.Simulation`: the start of a cycle
/// and a stop-the-world collection.
///
/// **The four collector lemmas of `GC.Gen.Run.Simulation` are false as
/// stated**; they stay admitted there.  Counterexamples (each a well-formed
/// program and a run carrying it out):
///
///   * `start_keeps_sim_inv`, `full_gc_collects` -- **inexact infix
///     pointers.**  `I.valid_value` asks of `Ptr { head = C; k }` (k > 0)
///     only that field `k - 1` of the closure `C` is a word `hdr` with
///     `getTag hdr == Infix_tag`.  The real heap resolves the pointer
///     `C + 8k` through `hdr`'s size (`resolve_object`: `C + 8k - 8 *
///     getWosize hdr`).  Program: allocate `Z` (one field, `Word 1`);
///     allocate a closure `C` of size 2 with fields `[Word hdr; Word 1]`,
///     where `getWosize hdr = (C + 8 - Z) / 8` (both major allocations, `Z`
///     below `C`); `SetRoots [Ptr { C; 1 }]`.  The real root `C + 8`
///     resolves to `Z`, and passes `root_valid_for_darkening`.  At
///     `StartCycle`, the snapshot is `{Z}`, but `C` is reachable in the
///     ideal memory and has an id: `reachable_in_kept` fails.  After
///     `full_gc`, `Z` keeps id 0, unreachable in the ideal memory (and `C`
///     is freed although the program reaches it).
///   * `slice_keeps_sim_inv` -- **partly swept garbage.**  `copies_faithful`
///     covers every block with an id, dead ones included.  Two blocks `y < x`,
///     unreachable when the cycle starts, `x` pointing at `y`; a sweep slice
///     whose budget reaches past `y` but not `x` frees `y` and drops its id,
///     while `x` stays allocated (white, ahead of the cursor) with a field
///     whose `Ptr` target has no block: `value_rep` fails for `x`.
///   * `minor_keeps_sim_inv` -- **words that look young.**  `I.Word w` only
///     excludes major-heap pointers (`~is_pointer_field w`); with
///     `minor_base_addr = 0` a word `w` in `[8, minor_heap_size)` is a
///     nursery address.  Program: allocate `A` in the nursery at offset `o`;
///     allocate `B` in the nursery with field `Word o` (allowed: `o` names a
///     nursery object, so `storable_value` holds); minor collection with root
///     `B`.  Cheney treats `o` as a pointer and rewrites `B`'s copy's field to
///     `A`'s promoted address, while the ideal field is still `Word o`.  (Even
///     with the fix, the proof also needs the fact that blocks pending free
///     mid-sweep hold no nursery pointers: they are not in the remembered
///     set, `ref_table_covers_with` covering only blocks not free at the
///     phase.)
///
/// Fixes (definition changes, for the integrator): `valid_value` should ask
/// `U64.v (getWosize hdr) == infix_offset` (OCaml's `Infix_offset_hd`); then
/// `infix_exact` below follows from `wf_memory`.  `copies_faithful` (or
/// `value_rep` on dead blocks) should be restricted to blocks whose objects
/// the program can reach, or allow dangling pointers in unreachable ones.
/// `Word` should also exclude young values (`~(GB.is_young w)`).
///
/// Proved here, under `infix_exact` (every infix pointer of the ideal
/// memory is exact: the word at `k - 1` has size `k`):
///   * `start_keeps_sim_inv_exact`: the start of a cycle keeps the joint
///     invariant -- it only recolours, and an object the program can reach
///     is reachable from the real roots in the real heap, so in the
///     snapshot;
///   * `full_gc_collects_exact`: after `full_gc`, a block holds an object
///     only if the program can still reach it -- an object reachable from
///     the real roots in the real heap is reachable in the ideal memory.

module GC.Gen.Run.Simulation.Collector

open FStar.Seq
open FStar.List.Tot
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.MinorHeap
open GC.Gen.Run.Step
open GC.Gen.Run.History
open GC.Gen.Run.Invariant
open GC.Model.Represents
open GC.Gen.Run.Simulation

module U64 = FStar.UInt64
module Ph = GC.Spec.Phase
module I = GC.Model.Ideal

/// An infix pointer is **exact**: the infix header at field `k - 1` of its
/// closure has size `k` (so the real pointer resolves to the closure).
let exact_value (im: I.ideal_memory) (v: I.value) : prop =
  match v with
  | I.Word _ -> True
  | I.Ptr { head; infix_offset } ->
      infix_offset > 0 ==>
        (I.valid_id im head /\ infix_offset < (Seq.index im.I.objects head).I.size /\
         (match I.field_at (Seq.index im.I.objects head) (infix_offset - 1) with
          | I.FValue (I.Word w) -> U64.v (getWosize w) == infix_offset
          | _ -> False))

/// Every root and every field of the ideal memory is exact.
let infix_exact (im: I.ideal_memory) : prop =
  (forall (i: nat). i < Seq.length im.I.roots ==> exact_value im (Seq.index im.I.roots i)) /\
  (forall (id: I.obj_id) (i: nat).
     I.valid_id im id /\ i < Seq.length (I.field_values (Seq.index im.I.objects id)) ==>
     exact_value im (Seq.index (I.field_values (Seq.index im.I.objects id)) i))

/// **The start of a cycle keeps the joint invariant**, infix pointers exact.
val start_keeps_sim_inv_exact (r: real_state) (h: cycle_history) (im: I.ideal_memory) (ids: block_id_map)
    (roots: seq U64.t) (r': real_state)
  : Lemma (requires sim_inv r h im ids /\ infix_exact im /\ roots_represented ids im.I.roots roots /\
                    step r (StartCycle roots) r')
          (ensures collector_post r h im ids (StartCycle roots) r')

/// **A stop-the-world collection leaves exactly what the program can
/// reach**, infix pointers exact.
val full_gc_collects_exact (#es0: list event) (#rs #rs': seq U64.t) (#r: real_state)
                           (rn: run (initial_state ()) (es0 @ full_gc_events rs rs') r)
                           (ps: list I.program_event)
  : Lemma (requires I.wf_program ps /\ executes rn ps /\ infix_exact (I.ideal_run ps))
          (ensures r.phase == Ph.Idle /\ r.memory.nursery == minor_reset r.memory.nursery /\
                   (forall (b: block_addr) (id: I.obj_id).
                      ids_of_run rn b == Some id ==> I.reachable (I.ideal_run ps) id))
