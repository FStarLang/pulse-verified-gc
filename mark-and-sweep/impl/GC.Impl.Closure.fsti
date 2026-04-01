(*
   Pulse GC - Closure Module Interface

   Handles OCaml closure and infix objects during GC.
*)

module GC.Impl.Closure

#lang-pulse

open FStar.Mul
open Pulse.Lib.Pervasives
open GC.Impl.Heap
open GC.Impl.Object
open GC.Impl.Fields
module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq

/// Read closure info value (field 2 of closure)
fn closinfo_val (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's **
           pure (spec_field_address (U64.v h_addr) 2 < heap_size)
  returns v: U64.t
  ensures is_heap heap 's

/// Extract start_env from closinfo
fn start_env_from_closinfo (closinfo: U64.t)
  requires emp
  returns start_env: U64.t
  ensures emp

/// Check if object is an infix object
fn is_infix_object (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's
  returns b: bool
  ensures is_heap heap 's

/// Check if object is a closure
fn is_closure_object (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's
  returns b: bool
  ensures is_heap heap 's

/// Get parent closure of infix object (returns None if offset invalid)
fn parent_closure_of_infix_opt (heap: heap_t) (infix_addr: hp_addr)
  requires is_heap heap 's
  returns parent_opt: option hp_addr
  ensures is_heap heap 's

/// Get parent closure of infix object (falls back to infix_addr)
fn parent_closure_of_infix (heap: heap_t) (infix_addr: hp_addr)
  requires is_heap heap 's
  returns parent: hp_addr
  ensures is_heap heap 's

/// Resolve object: if infix, return parent closure; otherwise return as-is
fn resolve_object (heap: heap_t) (obj: hp_addr)
  requires is_heap heap 's
  returns resolved: hp_addr
  ensures is_heap heap 's

/// Scan closure environment, calling callback for each pointer field
fn scan_closure_env (heap: heap_t) (h_addr: hp_addr) (wz: wosize)
                     (callback: U64.t -> stt unit (requires emp) (ensures fun _ -> emp))
  requires is_heap heap 's **
           pure (spec_field_address (U64.v h_addr) 2 < heap_size /\
                 spec_field_address (U64.v h_addr) (U64.v wz) < heap_size /\
                 U64.v wz >= 1 /\ U64.v wz <= pow2 54 - 1)
  ensures is_heap heap 's

/// Check if object has tag >= no_scan_tag
fn is_no_scan (heap: heap_t) (h_addr: hp_addr)
  requires is_heap heap 's
  returns b: bool
  ensures is_heap heap 's
