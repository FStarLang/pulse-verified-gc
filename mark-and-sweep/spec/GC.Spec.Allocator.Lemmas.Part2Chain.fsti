(*
   GC.Spec.Allocator.Lemmas.Part2Chain — Interface for read framing + chain_avoids proofs.
*)
module GC.Spec.Allocator.Lemmas.Part2Chain

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas.Core
module U64 = FStar.UInt64
module Seq = FStar.Seq

val alloc_spec_read_body : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) -> (addr: hp_addr) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword) /\
                  requested_wz >= 1 /\
                  (alloc_spec g fp requested_wz).obj_out <> 0UL /\
                  (let r = alloc_spec g fp requested_wz in
                   U64.v addr >= U64.v r.obj_out /\
                   U64.v addr + 8 <= U64.v r.obj_out + requested_wz * 8))
        (ensures (let r = alloc_spec g fp requested_wz in
                  read_word r.heap_out addr == read_word g addr))

val alloc_spec_read_other : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
                            (other: obj_addr) -> (addr: hp_addr) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword) /\
                  requested_wz >= 1 /\
                  Seq.mem other (objects zero_addr g) /\
                  chain_avoids g fp other (heap_size / U64.v mword) = true /\
                  U64.v addr >= U64.v other /\
                  U64.v addr + 8 <= U64.v other + U64.v (wosize_of_object other g) * 8)
        (ensures (let r = alloc_spec g fp requested_wz in
                  read_word r.heap_out addr == read_word g addr))

val alloc_spec_preserves_chain_avoids_other : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
                                              (excl: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword) /\
                  requested_wz >= 1 /\
                  chain_avoids g fp excl (heap_size / U64.v mword) = true /\
                  U64.v excl >= U64.v mword /\ U64.v excl < heap_size /\
                  U64.v excl % U64.v mword == 0 /\
                  Seq.mem (excl <: obj_addr) (objects zero_addr g))
        (ensures (let r = alloc_spec g fp requested_wz in
                  chain_avoids r.heap_out r.fp_out excl (heap_size / U64.v mword) = true))
