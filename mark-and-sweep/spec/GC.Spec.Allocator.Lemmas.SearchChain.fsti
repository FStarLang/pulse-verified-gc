module GC.Spec.Allocator.Lemmas.SearchChain

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq

val alloc_spec_preserves_fl_chain_terminates : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap g /\
                  GC.Spec.Allocator.Lemmas.Common.fl_valid g fp alloc_search_fuel /\
                  GC.Spec.Allocator.Lemmas.Chain.fl_chain_terminates g fp alloc_search_fuel)
        (ensures (let r = alloc_spec g fp requested_wz in
                  GC.Spec.Allocator.Lemmas.Chain.fl_chain_terminates r.heap_out r.fp_out alloc_search_fuel))
