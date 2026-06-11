module GC.Spec.Allocator.Lemmas.SearchBase

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq

val next_fp_in_objects : (g: heap) -> (obj: obj_addr) ->
  Lemma (requires well_formed_heap g /\
                  Seq.mem obj (objects zero_addr g) /\
                  U64.v (wosize_of_object obj g) >= 1 /\
                  (let hd = hd_address obj in
                   U64.v hd + 16 <= heap_size))
        (ensures (let next = read_word g obj in
                  is_pointer_field next ==>
                  Seq.mem next (objects zero_addr g)))

val alloc_from_block_objects_facts :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) ->
  Lemma (requires well_formed_heap g /\
                  Seq.mem obj (objects zero_addr g) /\
                  (let hdr = read_word g (hd_address obj) in
                   U64.v (getWosize hdr) >= wz) /\
                  (is_pointer_field next_fp ==> Seq.mem next_fp (objects zero_addr g)))
        (ensures (let (g', rem_fp) = alloc_from_block g obj wz next_fp in
                  (forall (h: obj_addr). Seq.mem h (objects zero_addr g) ==> Seq.mem h (objects zero_addr g')) /\
                  (is_pointer_field rem_fp ==> Seq.mem rem_fp (objects zero_addr g'))))

val alloc_split_fl_transfer_pre :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) -> (a: obj_addr) ->
  Lemma (requires GC.Spec.Allocator.Lemmas.Split.alloc_split_pre g obj wz next_fp /\
                    wz >= 1 /\
                    Seq.mem a (objects zero_addr g) /\
                    U64.v a >= U64.v mword /\
                    U64.v a < heap_size /\
                    U64.v a % U64.v mword = 0)
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    Seq.mem a (objects zero_addr g') /\
                    (U64.v (wosize_of_object a g) >= 1 ==>
                      U64.v (wosize_of_object a g') >= 1) /\
                    (U64.v (wosize_of_object a g) >= 1 /\
                     U64.v (hd_address a) + 16 <= heap_size ==>
                      read_word g' a == read_word g a)))

val alloc_exact_fl_transfer_pre :
  (g: heap) -> (obj: obj_addr) -> (wz: nat) -> (next_fp: U64.t) -> (a: obj_addr) ->
  Lemma (requires well_formed_heap g /\
                    Seq.mem obj (objects zero_addr g) /\
                    (let hdr = read_word g (hd_address obj) in
                     let block_wz = U64.v (getWosize hdr) in
                     block_wz >= wz /\ block_wz - wz < 2) /\
                    Seq.mem a (objects zero_addr g) /\
                    U64.v a >= U64.v mword /\
                    U64.v a < heap_size /\
                    U64.v a % U64.v mword = 0)
          (ensures (let (g', _) = alloc_from_block g obj wz next_fp in
                    Seq.mem a (objects zero_addr g') /\
                    (U64.v (wosize_of_object a g) >= 1 ==>
                      U64.v (wosize_of_object a g') >= 1) /\
                    (U64.v (wosize_of_object a g) >= 1 /\
                     U64.v (hd_address a) + 16 <= heap_size ==>
                      read_word g' a == read_word g a)))
