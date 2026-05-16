(*
   GC.Spec.Allocator.Lemmas.Part2Rest — Interface for wfh_part4 + read_field + blue + no_black proofs.
*)
module GC.Spec.Allocator.Lemmas.Part2Rest

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
open GC.Spec.Allocator.Lemmas.Core
module U64 = FStar.UInt64
module Seq = FStar.Seq

val alloc_spec_preserves_wfh_part4 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  well_formed_heap_part4 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword))
        (ensures (let r = alloc_spec g fp requested_wz in
                  well_formed_heap_part4 r.heap_out))

val alloc_spec_read_field_gt0 :
  (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  (src: obj_addr) -> (j: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword) /\
                  requested_wz >= 1 /\
                  (alloc_spec g fp requested_wz).obj_out <> 0UL /\
                  Seq.mem src (objects zero_addr g) /\
                  src <> (alloc_spec g fp requested_wz).obj_out /\
                  j > 0 /\
                  j < U64.v (wosize_of_object src g) /\
                  U64.v src + j * 8 + 8 <= heap_size)
        (ensures (let r = alloc_spec g fp requested_wz in
                  let addr : hp_addr = U64.uint_to_t (U64.v src + j * 8) in
                  read_word r.heap_out addr == read_word g addr))

val alloc_from_block_rem_in_objects_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   let bwz = U64.v (getWosize hdr) in
                   bwz >= wz /\ bwz - wz >= 2))
        (ensures (let (g', rem_fp) = alloc_from_block g obj wz next_fp in
                  is_pointer_field rem_fp /\
                  Seq.mem rem_fp (objects zero_addr g')))

val alloc_from_block_preserves_objects_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   U64.v (getWosize hdr) >= wz))
        (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                  (forall (h: obj_addr). Seq.mem h (objects zero_addr g) ==> Seq.mem h (objects zero_addr g'))))

val alloc_spec_new_objects_blue_part1 :
  (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword) /\
                  requested_wz >= 1 /\
                  (alloc_spec g fp requested_wz).obj_out <> 0UL)
        (ensures (let r = alloc_spec g fp requested_wz in
                  forall (x: obj_addr).
                    Seq.mem x (objects zero_addr r.heap_out) /\
                    ~(Seq.mem x (objects zero_addr g)) ==>
                    is_blue x r.heap_out = true))

val alloc_from_block_objects_backward_part1 :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) -> (h: obj_addr) ->
  Lemma (requires well_formed_heap_part1 g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   let bwz = U64.v (getWosize hdr) in
                   bwz >= wz /\ wz >= 1 /\ bwz - wz >= 2) /\
                  (let (g', _) = alloc_from_block g obj wz next_fp in
                   Seq.mem h (objects zero_addr g') /\
                   ~(Seq.mem h (objects zero_addr g))))
        (ensures h == snd (alloc_from_block g obj wz next_fp))

val alloc_spec_preserves_no_black_part1 : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires GC.Spec.Mark.no_black_objects g /\
                  well_formed_heap_part1 g /\
                  fl_valid g fp (heap_size / U64.v mword) /\
                  fl_chain_terminates g fp (heap_size / U64.v mword))
        (ensures (let r = alloc_spec g fp requested_wz in
                  GC.Spec.Mark.no_black_objects r.heap_out))
