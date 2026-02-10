(*
   Pulse GC - Top-Level Module
   
   This module provides the top-level garbage collection entry point,
   combining mark and sweep phases.
   
   Based on: Proofs/Impl.GC_closure_infix_ver3.fst
*)

module Pulse.Lib.GC

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.GC.Heap
open Pulse.Lib.GC.Object
open Pulse.Lib.GC.Stack
open Pulse.Lib.GC.Mark
open Pulse.Lib.GC.Sweep
module U64 = FStar.UInt64
module SZ = FStar.SizeT

/// ---------------------------------------------------------------------------
/// Full GC
/// ---------------------------------------------------------------------------

/// Main garbage collection entry point
/// 1. Mark: darken roots, process gray stack
/// 2. Sweep: reset black objects to white
fn collect (heap: heap_t) (st: gray_stack)
  requires is_heap heap 's ** is_gray_stack st 'l
  ensures exists* s2. is_heap heap s2 ** (exists* l2. is_gray_stack st l2)
{
  // Mark phase (simplified - just wraps mark_loop)
  mark_loop heap st;
  
  // Sweep phase (reset colors)
  sweep heap
}
