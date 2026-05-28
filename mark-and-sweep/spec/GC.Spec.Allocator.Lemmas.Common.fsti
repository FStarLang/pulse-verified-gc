module GC.Spec.Allocator.Lemmas.Common

open GC.Spec.Base
open GC.Spec.Heap
open GC.Spec.Object
open GC.Spec.Fields
open GC.Spec.Allocator
module U64 = FStar.UInt64
module Seq = FStar.Seq

/// Free-list validity: each node is a valid object with wosize >= 1,
/// no self-loops, and the successor (if any) is also fl_valid.
val fl_valid (g: heap) (fp: U64.t) (fuel: nat) : Tot prop

/// fl_valid extractors
val fl_valid_gives_mem : (g: heap) -> (fp: U64.t) -> (fuel: nat) ->
  Lemma (requires fuel > 0 /\
                  U64.v fp >= U64.v mword /\
                  U64.v fp < heap_size /\
                  U64.v fp % U64.v mword = 0 /\
                  fl_valid g fp fuel)
        (ensures Seq.mem fp (objects zero_addr g))

val fl_valid_gives_wosize : (g: heap) -> (fp: U64.t) -> (fuel: nat) ->
  Lemma (requires fuel > 0 /\
                  U64.v fp >= U64.v mword /\
                  U64.v fp < heap_size /\
                  U64.v fp % U64.v mword = 0 /\
                  fl_valid g fp fuel)
        (ensures U64.v (wosize_of_object (fp <: obj_addr) g) >= 1)

/// fl_valid for next node.
val fl_valid_next : (g: heap) -> (fp: U64.t) -> (fuel: nat) ->
  Lemma (requires fuel > 0 /\
                  U64.v fp >= U64.v mword /\
                  U64.v fp < heap_size /\
                  U64.v fp % U64.v mword = 0 /\
                  fl_valid g fp fuel)
        (ensures (let obj : obj_addr = fp in
                  let hd = hd_address obj in
                  U64.v hd + 16 <= heap_size ==>
                  read_word g obj <> fp /\
                  fl_valid g (read_word g obj) (fuel - 1)))

/// fl_valid introduction: null pointer terminates the free list.
val fl_valid_null : (g: heap) -> (fuel: nat) ->
  Lemma (requires fuel > 0)
        (ensures fl_valid g 0UL fuel)

/// fl_valid introduction: a valid node with a valid successor.
val fl_valid_step : (g: heap) -> (fp: U64.t) -> (fuel: nat) ->
  Lemma (requires fuel > 0 /\
                  U64.v fp >= U64.v mword /\
                  U64.v fp < heap_size /\
                  U64.v fp % U64.v mword = 0 /\
                  Seq.mem fp (objects zero_addr g) /\
                  U64.v (wosize_of_object (fp <: obj_addr) g) >= 1 /\
                  (U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size ==>
                    read_word g (fp <: obj_addr) <> fp /\
                    fl_valid g (read_word g (fp <: obj_addr)) (fuel - 1)))
        (ensures fl_valid g fp fuel)

/// fl_valid eliminator: extract all components from fl_valid.
val fl_valid_elim : (g: heap) -> (fp: U64.t) -> (fuel: nat) ->
  Lemma (requires fuel > 0 /\
                  U64.v fp >= U64.v mword /\
                  U64.v fp < heap_size /\
                  U64.v fp % U64.v mword = 0 /\
                  fl_valid g fp fuel)
        (ensures Seq.mem fp (objects zero_addr g) /\
                 U64.v (wosize_of_object (fp <: obj_addr) g) >= 1 /\
                 (U64.v (hd_address (fp <: obj_addr)) + 16 <= heap_size ==>
                   read_word g (fp <: obj_addr) <> fp /\
                   fl_valid g (read_word g (fp <: obj_addr)) (fuel - 1)))

/// fl_valid base case: fuel = 0 makes fl_valid trivially true.
val fl_valid_zero : (g: heap) -> (fp: U64.t) ->
  Lemma (fl_valid g fp 0)

/// fl_valid terminal case: out of bounds, unaligned, or null pointer.
val fl_valid_terminal : (g: heap) -> (fp: U64.t) -> (fuel: nat) ->
  Lemma (requires fuel > 0 /\
                  (fp = 0UL \/ U64.v fp < U64.v mword \/ U64.v fp >= heap_size \/
                   U64.v fp % U64.v mword <> 0))
        (ensures fl_valid g fp fuel)

/// fl_valid monotonicity: more fuel implies less fuel.
val fl_valid_weaken : (g: heap) -> (fp: U64.t) -> (fuel_strong: nat) -> (fuel_weak: nat) ->
  Lemma (requires fl_valid g fp fuel_strong /\ fuel_weak <= fuel_strong)
        (ensures fl_valid g fp fuel_weak)
