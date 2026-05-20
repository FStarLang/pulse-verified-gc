/// ---------------------------------------------------------------------------
/// GC.Gen.Impl.Iso — Implementation of minor_collect_with_iso
/// ---------------------------------------------------------------------------
///
/// Calls minor_collect (the operational implementation) then applies the
/// pure isomorphism theorem (minor_collect_iso_theorem) to establish the
/// graph-theoretic correctness property in the postcondition.

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
/// Implementation: call minor_collect then apply the isomorphism theorem
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 20 --fuel 0 --ifuel 0"
fn minor_collect_with_iso (gh: gen_heap_t)
                           (roots: array U64.t) (nroots: SZ.t)
                           (fwd_arr: array U64.t)
  requires is_gen_heap gh 'd 'b 's 'fp **
           pts_to roots 'rs **
           pts_to fwd_arr 'farr **
           pure (
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
      IsoThm.minor_collect_correctness minor_st 's 'fp 'rs)
{
  // Step 1: Call the operational minor_collect implementation
  minor_collect gh roots nroots fwd_arr;

  // Step 2: Apply the isomorphism theorem (pure lemma call)
  // The iso preconditions are about the inputs (minor, major, fp, roots),
  // which we have from our requires clause.
  IsoThm.minor_collect_iso_theorem
    ({ data = 'd; bump = 'b } <: minor_state) 's 'fp 'rs;

  // The theorem's conclusion (minor_collect_correctness) talks about
  // cheney_collect_spec's output, which equals s2 by the operational
  // postcondition from minor_collect.
  ()
}
#pop-options
