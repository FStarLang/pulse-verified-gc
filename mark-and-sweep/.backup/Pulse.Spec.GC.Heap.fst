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

/// Read a 64-bit word from heap at byte index (little-endian)
let read_word (g: heap) (addr: hp_addr) : U64.t =
  let word_bytes = Seq.slice g (U64.v addr) (U64.v addr + U64.v mword) in
  uint64_of_le word_bytes

/// ---------------------------------------------------------------------------
/// Range Replacement (for writes)
/// ---------------------------------------------------------------------------

/// Replace 8 bytes starting at addr with new bytes
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

/// Write a 64-bit word to heap at byte index (little-endian)
let write_word (g: heap) (addr: hp_addr) (value: U64.t) 
  : Pure heap
         (requires True)
         (ensures fun result ->
           Seq.length result == Seq.length g /\
           read_word result addr == value)
  =
  let bytes = le_of_uint64 value in
  let result = replace_range g addr bytes in
  // Prove that reading back gives the same value
  assert (Seq.equal (Seq.slice result (U64.v addr) (U64.v addr + U64.v mword)) bytes);
  result

/// ---------------------------------------------------------------------------
/// Read/Write Lemmas
/// ---------------------------------------------------------------------------

/// Reading after writing to same address returns written value
val read_write_same : (g: heap) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (read_word (write_word g addr v) addr == v)

#push-options "--z3rlimit 50"
let read_write_same g addr v = 
  // Follows from write_word postcondition
  ()
#pop-options

/// Reading after writing to different address returns original value
val read_write_different : (g: heap) -> (addr1: hp_addr) -> (addr2: hp_addr) -> (v: U64.t) ->
  Lemma (requires addr1 <> addr2 /\ 
                  (U64.v addr1 + U64.v mword <= U64.v addr2 \/
                   U64.v addr2 + U64.v mword <= U64.v addr1))
        (ensures read_word (write_word g addr1 v) addr2 == read_word g addr2)

let read_write_different g addr1 addr2 v =
  let g' = write_word g addr1 v in
  let slice1 = Seq.slice g (U64.v addr2) (U64.v addr2 + U64.v mword) in
  let slice2 = Seq.slice g' (U64.v addr2) (U64.v addr2 + U64.v mword) in
  assert (Seq.equal slice1 slice2)

/// Write to one address preserves reads before that address
val write_preserves_before : (g: heap) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (forall (a: hp_addr). U64.v a + U64.v mword <= U64.v addr ==>
           read_word (write_word g addr v) a == read_word g a)

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let write_preserves_before g addr v = 
  let prove_for_a (a: hp_addr) : Lemma 
    (requires U64.v a + U64.v mword <= U64.v addr)
    (ensures read_word (write_word g addr v) a == read_word g a)
    = read_write_different g addr a v
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove_for_a)
#pop-options

/// Write to one address preserves reads after that address
val write_preserves_after : (g: heap) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (forall (a: hp_addr). U64.v a >= U64.v addr + U64.v mword ==>
           read_word (write_word g addr v) a == read_word g a)

#push-options "--z3rlimit 50 --fuel 0 --ifuel 0"
let write_preserves_after g addr v = 
  let prove_for_a (a: hp_addr) : Lemma 
    (requires U64.v a >= U64.v addr + U64.v mword)
    (ensures read_word (write_word g addr v) a == read_word g a)
    = read_write_different g addr a v
  in
  FStar.Classical.forall_intro (FStar.Classical.move_requires prove_for_a)
#pop-options

/// Combined: write only affects the target address
val write_word_locality : (g: heap) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (forall (a: hp_addr). 
           (U64.v a + U64.v mword <= U64.v addr \/ U64.v a >= U64.v addr + U64.v mword) ==>
           read_word (write_word g addr v) a == read_word g a)

let write_word_locality g addr v =
  write_preserves_before g addr v;
  write_preserves_after g addr v

/// ---------------------------------------------------------------------------
/// Address Conversion Helpers
/// ---------------------------------------------------------------------------

/// Header address from field address (field = header + mword)
let hd_address (f_addr: val_addr) : hp_addr =
  U64.sub f_addr mword

/// Field address from header address  
let f_address (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) : val_addr =
  U64.add h_addr mword

/// Round-trip lemmas
val hd_f_roundtrip : (h: hp_addr{U64.v h + U64.v mword < heap_size}) ->
  Lemma (hd_address (f_address h) == h)

let hd_f_roundtrip h = ()

val f_hd_roundtrip : (f: val_addr{U64.v f + U64.v mword <= heap_size}) ->
  Lemma (f_address (hd_address f) == f)

let f_hd_roundtrip f = ()
