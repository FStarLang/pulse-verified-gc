(*
   GC.Spec.Allocator.Lemmas.Part2FL — Interface for fl_chain_terminates + obj_not_in_chain proofs.
*)
module GC.Spec.Allocator.Lemmas.Part2FL

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas.Core
module U64 = FStar.UInt64

val alloc_spec_preserves_fl_chain_terminates_part1 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword))
        (ensures (let r = alloc_spec g fp requested_wz in
                  fl_chain_terminates r.heap_out r.fp_out (heap_size / U64.v mword)))

val alloc_spec_obj_not_in_chain_part1 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword) /\
                  requested_wz >= 1 /\
                  (alloc_spec g fp requested_wz).obj_out <> 0UL)
        (ensures (let r = alloc_spec g fp requested_wz in
                  chain_avoids r.heap_out r.fp_out r.obj_out (heap_size / U64.v mword) = true))
