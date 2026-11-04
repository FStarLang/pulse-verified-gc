/// ---------------------------------------------------------------------------
/// GC.Gen.TwoPassEquiv.Collect -- the two passes at a Cheney result
/// ---------------------------------------------------------------------------
///
/// The implementation rewrites the promoted objects' fields
/// (`update_promoted_iter`) and then the remembered slots
/// (`rewrite_slots_iter`).  This module proves that this is the pointer update
/// of `cheney_collect_spec_with free` for a definition `free` of what counts as
/// free in the pre-collection heap, given the write barrier's guarantees for
/// the same `free`
/// (`GC.Gen.RefTable`).

module GC.Gen.TwoPassEquiv.Collect

open FStar.Seq
module U64 = FStar.UInt64

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Gen.Base
open GC.Gen.MinorHeap
open GC.Gen.Promote
open GC.Gen.ForwardingArray
open GC.Gen.RefTable

module AllocLemmas = GC.Spec.Allocator.Lemmas
module CheneySpec = GC.Gen.Cheney
module CheneyPres = GC.Gen.CheneyPreservation
module CPForwarding = GC.Gen.CheneyPreservation.Forwarding
module CPInj = GC.Gen.CheneyPreservation.Injectivity
module TwoPass = GC.Gen.TwoPassEquiv

/// ---------------------------------------------------------------------------
/// The two passes are the collection's pointer update
/// ---------------------------------------------------------------------------

val two_pass_implies_collect_with
  (free: free_def) (minor: minor_state) (major_pre: heap) (fp: U64.t)
  (roots: seq U64.t)
  (farr: seq U64.t) (slots: seq U64.t) (n: nat)
  : Lemma
    (requires
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       Seq.length farr == fwd_array_size /\
       represents_fwd farr prom.fwd_map /\
       CPForwarding.fwd_valid_or_infix prom.fwd_map prom.major_final /\
       CPInj.fwd_normal_injective prom.fwd_map prom.major_final /\
       CheneySpec.fwd_bounded prom.fwd_map /\
       no_infix_block prom.major_final /\
       valid_slot_addrs slots n /\
       slots_pairwise_distinct slots n /\
       free_def_ok free /\
       GC.Gen.Promote.allocations_not_free free /\
       ref_table_sound_with free major_pre slots n /\
       ref_table_complete_with free major_pre prom.fwd_map slots n /\
       fwd_targets_stable prom.fwd_map /\
       blocks_fit prom.major_final /\
       blocks_fit major_pre /\ no_infix_block major_pre /\
       minor_infix_wf minor /\
       minor_wf minor /\
       chain_objects_blue major_pre fp /\
       AllocLemmas.fl_valid major_pre fp TwoPass.heap_fuel /\
       AllocLemmas.fl_chain_terminates major_pre fp TwoPass.heap_fuel))
    (ensures
      (let prom = CheneySpec.cheney_promote minor major_pre fp roots in
       rewrite_slots_iter
         (update_promoted_iter prom.major_final farr prom.fwd_map 0)
         prom.fwd_map slots n 0
       == (CheneySpec.cheney_collect_spec_with free minor major_pre fp roots).mc_major))
