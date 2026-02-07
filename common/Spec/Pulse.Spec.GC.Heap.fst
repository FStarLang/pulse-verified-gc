/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.Heap - Heap memory operations
/// ---------------------------------------------------------------------------
///
/// This module provides pure heap read/write operations:
/// - Read/write 64-bit words
/// - Memory preservation lemmas
///
/// Ported from: Proofs/Spec.Heap.fsti

module Pulse.Spec.GC.Heap

open FStar.Seq
open FStar.Mul
open FStar.Endianness

module U64 = FStar.UInt64
module U8 = FStar.UInt8

open Pulse.Spec.GC.Base

/// ---------------------------------------------------------------------------
/// Word Read Operations
/// ---------------------------------------------------------------------------

let read_word (g: heap) (addr: hp_addr) : U64.t =
  let word_bytes = Seq.slice g (U64.v addr) (U64.v addr + U64.v mword) in
  uint64_of_le word_bytes

/// ---------------------------------------------------------------------------
/// Range Replacement (for writes)
/// ---------------------------------------------------------------------------

let replace_range (g: heap) 
                  (addr: hp_addr) 
                  (bytes: seq U8.t{Seq.length bytes == U64.v mword})
  : Pure heap
         (requires True)
         (ensures fun result ->
           Seq.length result == Seq.length g /\
           (forall i. i >= U64.v addr /\ i < U64.v addr + U64.v mword ==>
             Seq.index result i == Seq.index bytes (i - U64.v addr)) /\
           (forall i. (i < U64.v addr \/ i >= U64.v addr + U64.v mword) /\ i < Seq.length g ==>
             Seq.index result i == Seq.index g i))
  =
  let before = Seq.slice g 0 (U64.v addr) in
  let after = Seq.slice g (U64.v addr + U64.v mword) (Seq.length g) in
  Seq.append before (Seq.append bytes after)

/// ---------------------------------------------------------------------------
/// Word Write Operations
/// ---------------------------------------------------------------------------

let write_word (g: heap) (addr: hp_addr) (value: U64.t) 
  : Pure heap
         (requires True)
         (ensures fun result ->
           Seq.length result == Seq.length g /\
           read_word result addr == value)
  =
  let bytes = le_of_uint64 value in
  let result = replace_range g addr bytes in
  assert (Seq.equal (Seq.slice result (U64.v addr) (U64.v addr + U64.v mword)) bytes);
  result

/// ---------------------------------------------------------------------------
/// Read/Write Lemmas
/// ---------------------------------------------------------------------------

#push-options "--z3rlimit 50"
let read_write_same g addr v = ()
#pop-options

let read_write_different g addr1 addr2 v =
  let g' = write_word g addr1 v in
  let slice1 = Seq.slice g (U64.v addr2) (U64.v addr2 + U64.v mword) in
  let slice2 = Seq.slice g' (U64.v addr2) (U64.v addr2 + U64.v mword) in
  assert (Seq.equal slice1 slice2)

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let write_preserves_before g addr v = 
  let prove_for_a (a: hp_addr) : Lemma 
    (requires U64.v a + U64.v mword <= U64.v addr)
    (ensures read_word (write_word g addr v) a == read_word g a)
    = read_write_different g addr a v
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove_for_a)
#pop-options

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let write_preserves_after g addr v = 
  let prove_for_a (a: hp_addr) : Lemma 
    (requires U64.v a >= U64.v addr + U64.v mword)
    (ensures read_word (write_word g addr v) a == read_word g a)
    = read_write_different g addr a v
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove_for_a)
#pop-options

let write_word_locality g addr v =
  write_preserves_before g addr v;
  write_preserves_after g addr v

/// ---------------------------------------------------------------------------
/// Address Conversion Helpers
/// ---------------------------------------------------------------------------

let hd_address (obj: obj_addr) : hp_addr =
  U64.sub obj mword

let hd_address_bounds (obj: obj_addr) 
  : Lemma (U64.v (hd_address obj) + U64.v mword < heap_size) = 
  // obj >= 8 and obj < heap_size (from obj_addr type)
  // hd_address obj = obj - 8
  // (obj - 8) + 8 = obj < heap_size
  ()

let f_address (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) : obj_addr =
  U64.add h_addr mword

let hd_f_roundtrip h = ()

let f_hd_roundtrip f = 
  hd_address_bounds f

let hd_address_spec (obj: obj_addr) 
  : Lemma (U64.v (hd_address obj) = U64.v obj - 8)
  = ()

let hd_address_injective (f1: obj_addr) (f2: obj_addr) = 
  // hd_address f = f - 8
  // If f1 <> f2, then (f1 - 8) <> (f2 - 8) since subtraction preserves inequality
  ()
