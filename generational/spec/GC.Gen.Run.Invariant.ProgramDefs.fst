/// ---------------------------------------------------------------------------
/// GC.Gen.Run.Invariant.ProgramDefs - the run invariant, restated for the
/// program-step proofs
/// ---------------------------------------------------------------------------
///
/// `GC.Gen.Run.Invariant.fst` calls the proofs of its program-step lemmas
/// (`GC.Gen.Run.Invariant.Write`, `GC.Gen.Run.Invariant.Allocator`), so
/// those modules cannot open `GC.Gen.Run.Invariant` (F* rejects the cycle).
/// The invariant itself is `GC.Gen.Run.Invariant.Defs`'s (named again here);
/// this module repeats, word for word, the other definitions of
/// `GC.Gen.Run.Invariant.fsti` they are stated with (`stores_in_kept`,
/// `alloc_then_init`); `GC.Gen.Run.Invariant.fst` relates the two by
/// unfolding (`same_defs`, `same_alloc_then_init` there).  Change both
/// together.

module GC.Gen.Run.Invariant.ProgramDefs

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
module I = GC.Model.Ideal

let phase_shape (r: real_state) : prop = GC.Gen.Run.Invariant.Defs.phase_shape r

let snapshot_accounting (r: real_state) (h: cycle_history) : prop =
  GC.Gen.Run.Invariant.Defs.snapshot_accounting r h

let run_invariant (r: real_state) (h: cycle_history) : prop =
  GC.Gen.Run.Invariant.Defs.run_invariant r h

let in_kept (r: real_state) (h: cycle_history) (v: U64.t) : prop =
  is_pointer v ==> kept h (resolve_object (v <: obj_addr) r.memory.major)

let stores_in_kept (r: real_state) (h: cycle_history) (e: event) : prop =
  match e with
  | Alloc _ tag _ init ->
      I.tag_scannable tag ==> (forall (i: nat). i < Seq.length init ==> in_kept r h (Seq.index init i))
  | Write (Major x) _ v -> kept h x /\ (scannable r.memory.major x ==> in_kept r h v)
  | Write (Nursery o) _ v -> minor_tag r.memory.nursery o < 251 ==> in_kept r h v
  | _ -> True

let rec write_major_fields (g: heap) (a: U64.t) (init: seq U64.t) (i: nat)
  : GTot heap (decreases (Seq.length init - i)) =
  if i >= Seq.length init then g
  else
    let p = U64.v a + 8 * i in
    let g' = if p + 8 <= heap_size && p % 8 = 0 then write_word g (U64.uint_to_t p) (Seq.index init i) else g in
    write_major_fields g' a init (i + 1)

let alloc_then_init (r: real_state) (tag: I.tag_t) (size: nat) (init: seq U64.t) : GTot real_state =
  let res = AC.alloc_phase r.memory.major r.free_list r.phase size tag in
  let a = res.SA.obj_out in
  { r with memory = { r.memory with major = write_major_fields res.SA.heap_out a init 0 };
           free_list = res.SA.fp_out;
           ref_table = if U64.v a >= U64.v mword && U64.v a < heap_size && U64.v a % 8 = 0
                       then Seq.append r.ref_table (young_slots (a <: obj_addr) init)
                       else r.ref_table }
