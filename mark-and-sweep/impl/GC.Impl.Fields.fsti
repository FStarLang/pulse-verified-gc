(*
   Pulse GC - Fields Module Interface

   Exposes field address computation, field reads, pointer checks,
   and object iteration. Pure helpers (spec_field_address, lemmas)
   are also exported for use in pre/postconditions.
*)

module GC.Impl.Fields

#lang-pulse

open FStar.Mul
open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq

/// ---------------------------------------------------------------------------
/// Pure Helpers
/// ---------------------------------------------------------------------------

/// Spec-level field address: h_addr + i * 8
let spec_field_address (h_addr: nat) (i: nat) : nat =
  h_addr + i * 8

val lemma_mword_is_8 : unit -> Lemma (U64.v mword == 8)

val lemma_field_offset_no_overflow : (i: nat) ->
  Lemma (requires i <= pow2 54 - 1) (ensures i * 8 < pow2 64)

val lemma_address_add_no_overflow : (addr: nat) -> (offset: nat) ->
  Lemma (requires addr < heap_size /\ offset <= pow2 57)
        (ensures addr + offset < pow2 64)

val lemma_object_size_no_overflow : (wz: nat) ->
  Lemma (requires wz <= pow2 54 - 1)
        (ensures (1 + wz) * 8 <= pow2 57 /\ (1 + wz) * 8 < pow2 64)

val lemma_field_addr_aligned : (h_addr: nat) -> (i: nat) ->
  Lemma (requires h_addr % 8 == 0) (ensures (h_addr + i * 8) % 8 == 0)

/// Pure field address computation
val field_address_pure (h_addr: hp_addr) (i: U64.t{U64.v i >= 1 /\ U64.v i <= pow2 54 - 1})
  : Pure U64.t
    (requires True)
    (ensures fun addr -> U64.v addr == spec_field_address (U64.v h_addr) (U64.v i))

/// ---------------------------------------------------------------------------
/// Pulse Functions
/// ---------------------------------------------------------------------------

/// Read field i of object at h_addr
fn read_field (heap: heap_t) (h_addr: hp_addr) (i: U64.t)
  requires is_heap heap 's **
           pure (U64.v i >= 1 /\
                 U64.v i <= pow2 54 - 1 /\
                 spec_field_address (U64.v h_addr) (U64.v i) + 8 <= heap_size)
  returns v: U64.t
  ensures is_heap heap 's **
          pure (U64.v i >= 1 /\
                spec_field_address (U64.v h_addr) (U64.v i) + 8 <= Seq.length 's /\
                v == spec_read_word 's (spec_field_address (U64.v h_addr) (U64.v i)))

/// Read successor pointer at field i
fn read_succ (heap: heap_t) (h_addr: hp_addr) (i: U64.t)
  requires is_heap heap 's **
           pure (U64.v i >= 1 /\
                 U64.v i <= pow2 54 - 1 /\
                 spec_field_address (U64.v h_addr) (U64.v i) + 8 <= heap_size)
  returns succ: U64.t
  ensures is_heap heap 's

/// Check if a value is a valid heap pointer
fn is_pointer (v: U64.t)
  requires emp
  returns b: bool
  ensures emp ** pure (b <==> (U64.v v > 0 /\
                               U64.v v < heap_size /\
                               U64.v v % U64.v mword == 0))

/// Check if an address contains a valid object header
fn is_valid_header (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's
  returns b: bool
  ensures is_heap heap 's

/// Compute address of next object given current object's header address
fn next_object_addr (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's
  returns addr: U64.t
  ensures is_heap heap 's
