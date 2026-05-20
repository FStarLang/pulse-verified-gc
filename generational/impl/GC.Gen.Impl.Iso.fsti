/// ---------------------------------------------------------------------------
/// GC.Gen.Impl.Iso — Minor collection with graph isomorphism correctness
/// ---------------------------------------------------------------------------
///
/// Wraps GC.Gen.Impl.minor_collect with the graph isomorphism theorem from
/// GC.Gen.MinorCollectIso, providing a single function whose postcondition
/// guarantees both:
///   - Operational correctness (result = cheney_collect_spec output)
///   - Graph-theoretic correctness (8-property isomorphism A-H)
///
/// The precondition is the union of:
///   - The implementation's mechanical requirements (array sizes, zeroing, etc.)
///   - The isomorphism theorem's logical preconditions (field_correspondence,
///     well_formed_heap of the spec output, graph_wf, etc.)
///
/// NOTE: Several iso preconditions refer to the spec output (mc_major). Since
/// cheney_collect_spec is a pure function of the inputs, these CAN appear in a
/// requires clause. However, the caller must establish them (they are not derived
/// internally). Future work: prove these from operational invariants.

module GC.Gen.Impl.Iso

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Base
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Impl.MinorHeap
open GC.Impl.Heap
module SpecFields = GC.Spec.Fields
module AllocLemmas = GC.Spec.Allocator.Lemmas
module CheneySpec = GC.Gen.Cheney
module PromoteSpec = GC.Gen.Promote
module UpdatePtrs = GC.Gen.Impl.UpdatePtrs
module IsoThm = GC.Gen.MinorCollectIso
module Mark = GC.Spec.Mark

open GC.Gen.Impl

/// ---------------------------------------------------------------------------
/// Minor collection with isomorphism guarantee
/// ---------------------------------------------------------------------------

/// Performs minor collection AND proves that the result is a graph isomorphism
/// of the pre-GC combined graph.
///
/// Postcondition includes BOTH:
///   1. Operational refinement: s2 == cheney_collect_spec(...).mc_major, etc.
///   2. Isomorphism correctness: minor_collect_correctness (properties A-H)
///
/// Precondition is the union of the implementation requirements and the
/// isomorphism theorem's preconditions. The iso preconditions include some
/// facts about the spec output (e.g., well_formed_heap res.mc_major); since
/// cheney_collect_spec is a pure function of the inputs, these are well-typed
/// but must be established by the caller.
fn minor_collect_with_iso (gh: gen_heap_t)
                           (roots: array U64.t) (nroots: SZ.t)
                           (fwd_arr: array U64.t)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pure (
             // === Implementation preconditions ===
             // (same as minor_collect in GC.Gen.Impl.fsti)
             SpecFields.well_formed_heap 's /\
             AllocLemmas.fl_valid 's 'fp (heap_size / U64.v mword) /\
             AllocLemmas.fl_chain_terminates 's 'fp (heap_size / U64.v mword) /\
             PromoteSpec.heap_objects_dense 's /\
             PromoteSpec.chain_objects_blue 's 'fp /\
             SZ.v nroots == Seq.length 'rs /\
             Seq.length 'farr == UpdatePtrs.fwd_array_size /\
             (forall (i: nat). i < Seq.length 'farr ==> Seq.index 'farr i == 0UL) /\
             minor_wf ({ data = 'd; bump = 'b }) /\
             minor_guards_complete ({ data = 'd; bump = 'b }) /\
             Seq.length (SpecFields.objects zero_addr 's) > 0 /\

             // === Isomorphism theorem preconditions ===
             // (from GC.Gen.MinorCollectIso.minor_collect_iso_preconditions)
             IsoThm.minor_collect_iso_preconditions
               ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs)
  ensures exists* d2 b2 s2 fp2 rs2 farr2.
    is_gen_heap gh d2 b2 s2 fp2 **
    pts_to roots rs2 **
    pts_to fwd_arr farr2 **
    pure (
      let minor_st : minor_state = { data = 'd; bump = 'b } in
      let res = CheneySpec.cheney_collect_spec minor_st 's 'fp 'rs in
      let prom = CheneySpec.cheney_promote minor_st 's 'fp 'rs in

      // --- Operational postconditions (from minor_collect) ---
      s2 == res.mc_major /\
      fp2 == res.mc_fp /\
      rs2 == res.mc_roots /\
      U64.v b2 == 0 /\
      (forall (x: obj_addr). Seq.mem x (SpecFields.objects zero_addr 's) ==>
        Seq.mem x (SpecFields.objects zero_addr s2)) /\
      rs2 == PromoteSpec.rewrite_roots 'rs prom.fwd_map /\
      SpecFields.well_formed_heap_part1 s2 /\
      AllocLemmas.fl_valid s2 fp2 (heap_size / U64.v mword) /\
      AllocLemmas.fl_chain_terminates s2 fp2 (heap_size / U64.v mword) /\

      // --- Graph isomorphism correctness (from MinorCollectIso) ---
      // Properties A-H: injectivity, image validity, edge forward/backward,
      // header preservation, object survival, forward reachability, surjectivity
      IsoThm.minor_collect_correctness minor_st 's 'fp 'rs)
