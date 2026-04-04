(*
   GC.Spec.Allocator.Lemmas — Interface for allocator-GC bridge proofs.

   Main theorem: alloc_spec preserves well_formed_heap, so the GC can be
   called after any sequence of allocations.
*)
module GC.Spec.Allocator.Lemmas

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq

/// alloc_from_block preserves well_formed_heap
val alloc_from_block_preserves_wf :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap g /\
                  Seq.mem obj (objects 0UL g) /\
                  (let hdr = read_word g (hd_address obj) in
                   U64.v (getWosize hdr) >= wz) /\
                  (is_pointer_field next_fp ==> Seq.mem next_fp (objects 0UL g)))
        (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                  well_formed_heap g'))

/// Free-list validity: each node is a valid object with wosize >= 1,
/// no self-loops, and the successor (if any) is also fl_valid.
val fl_valid (g: heap) (fp: U64.t) (fuel: nat) : Tot prop (decreases fuel)

/// fl_valid extractors
val fl_valid_gives_mem : (g: heap) -> (fp: U64.t) -> (fuel: nat) ->
  Lemma (requires fuel > 0 /\
                  U64.v fp >= U64.v mword /\
                  U64.v fp < heap_size /\
                  U64.v fp % U64.v mword = 0 /\
                  fl_valid g fp fuel)
        (ensures Seq.mem fp (objects 0UL g))

val fl_valid_gives_wosize : (g: heap) -> (fp: U64.t) -> (fuel: nat) ->
  Lemma (requires fuel > 0 /\
                  U64.v fp >= U64.v mword /\
                  U64.v fp < heap_size /\
                  U64.v fp % U64.v mword = 0 /\
                  fl_valid g fp fuel)
        (ensures U64.v (wosize_of_object (fp <: obj_addr) g) >= 1)

/// **Main theorem**: alloc_spec preserves well_formed_heap.
/// Given a well-formed heap and a valid free list, allocation produces
/// a well-formed heap suitable for subsequent GC collection.
val alloc_spec_preserves_wf : (g: heap) -> (fp: U64.t) -> (requested_wz: nat) ->
  Lemma (requires well_formed_heap g /\
                  fl_valid g fp (heap_size / U64.v mword))
        (ensures (let r = alloc_spec g fp requested_wz in
                  well_formed_heap r.heap_out))
