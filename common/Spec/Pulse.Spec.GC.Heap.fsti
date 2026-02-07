/// ---------------------------------------------------------------------------
/// Pulse.Spec.GC.Heap - Heap memory operations
/// ---------------------------------------------------------------------------
///
/// This module provides pure heap read/write operations:
/// - Read/write 64-bit words
/// - Memory preservation lemmas

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
val read_word (g: heap) (addr: hp_addr) : U64.t

/// ---------------------------------------------------------------------------
/// Range Replacement (for writes)
/// ---------------------------------------------------------------------------

/// Replace 8 bytes starting at addr with new bytes
val replace_range (g: heap) 
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

/// ---------------------------------------------------------------------------
/// Word Write Operations
/// ---------------------------------------------------------------------------

/// Write a 64-bit word to heap at byte index (little-endian)
val write_word (g: heap) (addr: hp_addr) (value: U64.t) 
  : Pure heap
         (requires True)
         (ensures fun result ->
           Seq.length result == Seq.length g /\
           read_word result addr == value)

/// ---------------------------------------------------------------------------
/// Read/Write Lemmas
/// ---------------------------------------------------------------------------

/// Reading after writing to same address returns written value
val read_write_same : (g: heap) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (read_word (write_word g addr v) addr == v)

/// Reading after writing to different address returns original value
val read_write_different : (g: heap) -> (addr1: hp_addr) -> (addr2: hp_addr) -> (v: U64.t) ->
  Lemma (requires addr1 <> addr2 /\ 
                  (U64.v addr1 + U64.v mword <= U64.v addr2 \/
                   U64.v addr2 + U64.v mword <= U64.v addr1))
        (ensures read_word (write_word g addr1 v) addr2 == read_word g addr2)

/// Write to one address preserves reads before that address
val write_preserves_before : (g: heap) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (forall (a: hp_addr). U64.v a + U64.v mword <= U64.v addr ==>
           read_word (write_word g addr v) a == read_word g a)

/// Write to one address preserves reads after that address
val write_preserves_after : (g: heap) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (forall (a: hp_addr). U64.v a >= U64.v addr + U64.v mword ==>
           read_word (write_word g addr v) a == read_word g a)

/// Combined: write only affects the target address
val write_word_locality : (g: heap) -> (addr: hp_addr) -> (v: U64.t) ->
  Lemma (forall (a: hp_addr). 
           (U64.v a + U64.v mword <= U64.v addr \/ U64.v a >= U64.v addr + U64.v mword) ==>
           read_word (write_word g addr v) a == read_word g a)

/// ---------------------------------------------------------------------------
/// Address Conversion Helpers
/// ---------------------------------------------------------------------------

/// Header address from object address (header = object - mword)
val hd_address (obj: obj_addr) : hp_addr

/// Helper: hd_address result satisfies f_address precondition
val hd_address_bounds : (obj: obj_addr) ->
  Lemma (U64.v (hd_address obj) + U64.v mword < heap_size)

/// Field/object address from header address  
val f_address (h_addr: hp_addr{U64.v h_addr + U64.v mword < heap_size}) : obj_addr

/// Round-trip lemmas
val hd_f_roundtrip : (h: hp_addr{U64.v h + U64.v mword < heap_size}) ->
  Lemma (hd_address (f_address h) == h)

val f_hd_roundtrip : (f: obj_addr) ->
  Lemma (ensures (hd_address_bounds f; f_address (hd_address f) == f))

/// hd_address arithmetic: hd_address obj = obj - 8
val hd_address_spec : (obj: obj_addr) ->
  Lemma (U64.v (hd_address obj) = U64.v obj - 8)

/// hd_address is injective: different addresses give different headers
val hd_address_injective : (f1: obj_addr) -> (f2: obj_addr) ->
  Lemma (requires f1 <> f2)
        (ensures hd_address f1 <> hd_address f2)
