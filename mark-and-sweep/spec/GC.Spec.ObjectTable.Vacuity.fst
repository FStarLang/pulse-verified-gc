/// ---------------------------------------------------------------------------
/// GC.Spec.ObjectTable.Vacuity - the object-start table lemmas are not vacuous
/// ---------------------------------------------------------------------------
///
/// For every new lemma with a non-trivial precondition, "the precondition
/// implies False" must fail: if it went through, the lemma would hold of no
/// state at all (mark-and-sweep/NOTES.md, "Vacuity checking").  Each check is
/// `expect_failure`, so the build fails if one of them ever succeeds.

module GC.Spec.ObjectTable.Vacuity

open FStar.Seq
open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.FreeLists
open GC.Spec.Allocator.Lists
open GC.Spec.ObjectTable
open GC.Gen.MinorHeap

module U64 = FStar.UInt64
module AL = GC.Gen.AllocLists
module PS = GC.Gen.Promote
module TS = GC.Spec.ObjectTable.Sweep
module Corr = GC.Spec.Correctness
module SpecSweep = GC.Spec.Sweep
module SpecCoalesce = GC.Spec.Coalesce
module HA = GC.Spec.HeapAgree
module FLs = GC.Spec.FreeLists

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"

[@@expect_failure [19]]
let table_ok_meaning_hyps_not_false (g: heap) (t: seq U64.t) (j: nat)
  : Lemma (requires table_ok g t /\ Seq.length (objects zero_addr g) > 0 /\ j < n_windows)
          (ensures False)
  = ()

[@@expect_failure [19]]
let table_add_block_hyps_not_false (g g2: heap) (t: seq U64.t) (p: obj_addr) (wz: nat)
  : Lemma (requires table_ok g t /\
                    heap_objects_dense g2 /\
                    Seq.mem p (objects zero_addr g2) /\
                    U64.v (wosize_of_object p g2) == wz /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                       Seq.mem x (objects zero_addr g2)) /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g2) ==>
                       Seq.mem x (objects zero_addr g) \/ x == p))
          (ensures False)
  = ()

[@@expect_failure [19]]
let fused_walk_hyps_not_false (g0 g: heap) (objs: seq obj_addr) (fb: U64.t) (rw: nat)
                              (start: nat)
  : Lemma (requires TS.fw_inv g0 g start objs fb rw /\ rw > 0)
          (ensures False)
  = ()

[@@expect_failure [19]]
let cursor_out_emit_step_hyps_not_false (g0: heap) (v: hp_addr)
  : Lemma (requires Seq.length (objects v g0) > 0)
          (ensures False)
  = ()

[@@expect_failure [19]]
let collect_table_ok_hyps_not_false (h_init h_mark: heap) (roots: seq obj_addr) (s2: heap)
                                    (t: seq U64.t)
  : Lemma (requires Corr.mark_post h_init h_mark roots 0UL /\
                    HA.heaps_agree_mod_free_links s2
                      (fst (SpecCoalesce.coalesce (fst (SpecSweep.sweep h_mark 0UL)))) /\
                    table_matches s2 t)
          (ensures False)
  = ()

[@@expect_failure [19]]
let alloc_lists_table_hyps_not_false (g: heap) (fls: fl_state) (wz: nat) (t: seq U64.t)
  : Lemma (requires AL.alloc_lists_pre g fls /\ wz >= 1 /\ table_ok g t)
          (ensures False)
  = ()

[@@expect_failure [19]]
let promote_object_sound_step_hyps_not_false
  (minor: minor_state) (major: heap) (obj: U64.t) (fp: fl_state) (wz: nat{wz > 0})
  (t t2: seq U64.t)
  : Lemma (requires AL.alloc_lists_pre major fp /\
                    (alloc_lists_spec major fp wz).obj_out <> 0UL /\
                    table_sound major t /\
                    table_sound (alloc_lists_spec major fp wz).heap_out t2)
          (ensures False)
  = ()

[@@expect_failure [19]]
let minor_collect_sound_hyps_not_false (minor: minor_state) (major: heap) (fp: fl_state)
                                       (roots: seq U64.t) (t: seq U64.t)
  : Lemma (requires (let prom = GC.Gen.Cheney.cheney_promote minor major fp roots in
                     well_formed_heap_part1 prom.PS.major_final /\
                     table_sound prom.PS.major_final t))
          (ensures False)
  = ()

/// The invariant that always holds, and its lemmas.

[@@expect_failure [19]]
let table_sound_meaning_hyps_not_false (g: heap) (t: seq U64.t) (j: nat)
  : Lemma (requires table_sound g t /\ Seq.length (objects zero_addr g) > 0 /\ j < n_windows)
          (ensures False)
  = ()

[@@expect_failure [19]]
let table_sound_grow_hyps_not_false (g1 g2: heap) (t: seq U64.t)
  : Lemma (requires table_sound g1 t /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g1) ==>
                       Seq.mem x (objects zero_addr g2)))
          (ensures False)
  = ()

[@@expect_failure [19]]
let table_matches_sound_hyps_not_false (g: heap) (t: seq U64.t)
  : Lemma (requires table_matches g t) (ensures False)
  = ()

[@@expect_failure [19]]
let table_sound_add_block_hyps_not_false (g g2: heap) (t: seq U64.t) (p: obj_addr) (wz: nat)
  : Lemma (requires table_sound g t /\
                    Seq.mem p (objects zero_addr g2) /\
                    (forall (x: obj_addr). Seq.mem x (objects zero_addr g) ==>
                       Seq.mem x (objects zero_addr g2)))
          (ensures False)
  = ()

[@@expect_failure [19]]
let alloc_lists_sound_hyps_not_false (g: heap) (fls: fl_state) (t: seq U64.t)
  : Lemma (requires AL.alloc_lists_pre g fls /\ table_sound g t)
          (ensures False)
  = ()

#pop-options
