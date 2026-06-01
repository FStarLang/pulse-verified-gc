module GC.Spec.Allocator.Lemmas.ObjNotInChain

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq

open GC.Spec.Allocator.Lemmas.Common
open GC.Spec.Allocator.Lemmas.Chain

/// **Theorem**: alloc_spec removes obj_out from the chain.
val alloc_spec_obj_not_in_chain : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap g /\
                  fl_valid g fp alloc_search_fuel /\
                  fl_chain_terminates g fp alloc_search_fuel /\
                  requested_wz >= 1 /\
                  (alloc_spec g fp requested_wz).obj_out <> 0UL)
        (ensures (let r = alloc_spec g fp requested_wz in
                  chain_avoids r.heap_out r.fp_out r.obj_out alloc_search_fuel = true))
