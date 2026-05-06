(*
   GC.Spec.Allocator.Lemmas.Part1 — Interface for Section P1 proofs.

   alloc_spec / alloc_from_block preserve object membership under
   well_formed_heap_part1 (weaker precondition than well_formed_heap).
*)
module GC.Spec.Allocator.Lemmas.Part1

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas
module U64 = FStar.UInt64
module Seq = FStar.Seq

/// **Theorem**: alloc_spec preserves object membership under just well_formed_heap_part1.
/// (Weaker precondition than alloc_spec_preserves_objects.)
val alloc_spec_preserves_objects_part1 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword))
        (ensures (let r = alloc_spec g fp requested_wz in
                  (forall (x: obj_addr). Seq.mem x (objects 0UL g) ==>
                    Seq.mem x (objects 0UL r.heap_out))))

/// **Theorem**: alloc_from_block preserves object membership under just
/// well_formed_heap_part1. (Public wrapper for internal part1 proof.)
val alloc_from_block_preserves_objects_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects 0UL g) /\
                  (let hdr = read_word g (hd_address obj) in
                   U64.v (getWosize hdr) >= wz))
        (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                  (forall (h: obj_addr). Seq.mem h (objects 0UL g) ==> Seq.mem h (objects 0UL g'))))

/// **Theorem**: In the split case (block_wz - wz >= 2), the remainder fp
/// returned by alloc_from_block is a valid pointer AND is in objects of
/// the output heap. Requires only well_formed_heap_part1.
val alloc_from_block_rem_in_objects_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects 0UL g) /\
                  (let hdr = read_word g (hd_address obj) in
                   let bwz = U64.v (getWosize hdr) in
                   bwz >= wz /\ bwz - wz >= 2))
        (ensures (let (g', rem_fp) = alloc_from_block g obj wz next_fp in
                  is_pointer_field rem_fp /\
                  Seq.mem rem_fp (objects 0UL g')))
