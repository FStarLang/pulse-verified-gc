/// ---------------------------------------------------------------------------
/// GC.Gen.CheneyEnd2End — Proofs
/// ---------------------------------------------------------------------------

module GC.Gen.CheneyEnd2End

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Graph
open GC.Spec.HeapModel
open GC.Spec.DFS
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.PromoteUpdate
open GC.Gen.Cheney

module MajorCorrectness = GC.Spec.Correctness
module HeapGraph = GC.Spec.HeapGraph
module AllocLemmas = GC.Spec.Allocator.Lemmas
module Mark = GC.Spec.Mark
module Sweep = GC.Spec.Sweep
module CheneyCorr = GC.Gen.CheneyCorrectness
module CheneyPres = GC.Gen.CheneyPreservation

/// ---------------------------------------------------------------------------
/// Post-minor preservation: no_black_objects
/// ---------------------------------------------------------------------------

/// Key insight: cheney_promote doesn't change colors of pre-existing objects
/// (it only writes into newly allocated blocks), and update_major_pointers
/// only writes field values (not headers). Promoted objects are white.

#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"

let cheney_collect_no_black
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  : Lemma (requires well_formed_heap major /\
                    AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
                    AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
                    Mark.no_black_objects major /\
                    minor_infix_wf minor)
          (ensures Mark.no_black_objects (cheney_collect_spec minor major fp roots).mc_major)
  =
  // Step 1: cheney_promote preserves no_black_objects
  CheneyPres.cheney_promote_preserves_no_black minor major fp roots;
  let prom = cheney_promote minor major fp roots in
  // Step 2: update_major_pointers preserves all headers →
  // no_black_objects is preserved (it only depends on headers)
  cheney_promote_preserves_wfh_part1 minor major fp roots;
  update_major_pointers_preserves_objects prom.major_final prom.fwd_map;
  // For each obj in objects(0UL, mc_major): header is same as in prom.major_final
  // (by update_major_pointers_preserves_header). Since no_black holds for
  // prom.major_final, it holds for mc_major.
  let m' = update_major_pointers prom.major_final prom.fwd_map in
  let aux (obj: obj_addr)
    : Lemma (requires Seq.mem obj (objects zero_addr m'))
            (ensures ~(is_black obj m'))
    [SMTPat (Seq.mem obj (objects zero_addr m'))]
    = assert (Seq.mem obj (objects zero_addr prom.major_final));
      update_major_pointers_preserves_header prom.major_final prom.fwd_map obj;
      // header unchanged → color predicates transfer
      color_of_header_eq obj m' prom.major_final
  in
  ()

#pop-options

/// ---------------------------------------------------------------------------
/// Main theorem: cheney_gc_end_to_end
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"

let cheney_gc_end_to_end
  (minor: minor_state) (major: heap) (fp: U64.t) (roots: seq U64.t)
  (major_stack: seq obj_addr) (major_fp: U64.t) (cap: nat)
  : Lemma
    (requires
      well_formed_heap major /\
      AllocLemmas.fl_valid major fp (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates major fp (heap_size / U64.v mword) /\
      chain_objects_blue major fp /\
      Mark.no_black_objects major /\
      minor_infix_wf minor /\
      well_formed_heap (cheney_collect_spec minor major fp roots).mc_major /\
      Mark.no_pointer_to_blue (cheney_collect_spec minor major fp roots).mc_major /\
      (let res = cheney_collect_spec minor major fp roots in
       Mark.stack_props res.mc_major major_stack /\
       Mark.root_props res.mc_major major_stack /\
       Sweep.fp_in_heap major_fp res.mc_major /\
       (forall (x: obj_addr). Seq.mem x (objects zero_addr res.mc_major) /\
         (is_gray x res.mc_major \/ is_black x res.mc_major) ==> Seq.mem x major_stack) /\
       (let g = create_graph res.mc_major in
        let roots' = HeapGraph.coerce_to_vertex_list major_stack in
        graph_wf g /\ is_vertex_set roots' /\ subset_vertices roots' g.vertices) /\
       Seq.length major_stack <= cap /\ cap > 0))
    (ensures
      (let minor_res = cheney_collect_spec minor major fp roots in
       let prom = cheney_promote minor major fp roots in
       MajorCorrectness.full_gc_correctness
         minor_res.mc_major
         (fst (Sweep.sweep (Mark.mark minor_res.mc_major major_stack) major_fp))
         major_stack /\
       (forall (x: obj_addr). Seq.mem x (objects zero_addr major) ==>
         Seq.mem x (objects zero_addr minor_res.mc_major)) /\
       well_formed_heap_part1 minor_res.mc_major /\
       AllocLemmas.fl_valid minor_res.mc_major minor_res.mc_fp (heap_size / U64.v mword) /\
       AllocLemmas.fl_chain_terminates minor_res.mc_major minor_res.mc_fp (heap_size / U64.v mword) /\
       minor_wf minor_res.mc_minor /\
       U64.v minor_res.mc_minor.bump == 0 /\
       minor_res.mc_roots == rewrite_roots roots prom.fwd_map))
  =
  let minor_res = cheney_collect_spec minor major fp roots in
  // --- Cheney minor collection correctness (from CheneyCorrectness) ---
  CheneyCorr.cheney_gc_correct minor major fp roots;
  // --- Major GC correctness ---
  // no_black_objects preservation
  cheney_collect_no_black minor major fp roots;
  // no_pointer_to_blue is a precondition on the post-minor heap
  // Now we have all preconditions for full_gc_correctness_from_end_to_end
  MajorCorrectness.full_gc_correctness_from_end_to_end
    minor_res.mc_major major_stack major_stack major_fp

#pop-options
