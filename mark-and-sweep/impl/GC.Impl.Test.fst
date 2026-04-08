(*
   GC.Impl.Test — Pulse round-trip integration test

   Demonstrates that init, allocate, and collect compose correctly
   at the implementation level, with postconditions connecting to
   the pure specification.

   Test 1: init → alloc (simple allocation)
   Test 2: init → collect(empty) → alloc (full GC cycle + allocation)
*)
module GC.Impl.Test

#lang-pulse

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"

open Pulse.Lib.Pervasives
open GC.Spec.Base
open GC.Impl.Heap
open GC.Impl.Object
open GC.Impl.Stack
open GC.Impl.Allocator
open GC.Impl

module U64 = FStar.UInt64
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec
module SpecAlloc = GC.Spec.Allocator
module SpecAllocLemmas = GC.Spec.Allocator.Lemmas
module SpecFields = GC.Spec.Fields
module SpecGCPost = GC.Spec.Correctness
module Bridge = GC.Test.Bridge
module Test = GC.Test

/// =========================================================================
/// Test 1: init → alloc (simple allocation from fresh heap)
/// =========================================================================
#push-options "--fuel 0 --ifuel 0 --z3rlimit 100"
fn test_init_alloc (_: unit)
  requires emp
  returns _: unit
  ensures emp
{
  // Create a zeroed heap and initialize the free list
  let heap = alloc_heap ();
  let fp0 = init_heap heap;

  // Bind ghost state: s0 = initialized heap
  with s0. assert (is_heap heap s0);

  // Prove well_formed_heap s0 for allocate's precondition
  Bridge.init_wf (Seq.create heap_size 0uy);

  // Allocate an object of wosize 2
  let res = allocate heap fp0 2UL;

  // Drop everything (demo only)
  with s1. assert (is_heap heap s1);
  drop_ (is_heap heap s1);
}
#pop-options

/// =========================================================================
/// Test 2: init → collect(empty roots) → alloc
/// =========================================================================
#push-options "--z3rlimit 100"
fn test_init_collect_alloc (_: unit)
  requires emp
  returns _: unit
  ensures emp
{
  // Create heap and initialize free list
  let heap = alloc_heap ();
  let fp0 = init_heap heap;

  // Bind ghost state
  with s0. assert (is_heap heap s0);

  // Create gray stack with heap_size entries (collect needs capacity >= heap_size)
  let stack_storage = V.alloc 0UL heap_size_sz;
  let st = create_stack stack_storage heap_size_sz;

  // Establish gc_precondition for the initialized heap with empty roots
  // init_enables_collect proves: mark_inv, fp_valid, root_props,
  //   no_black, no_pointer_to_blue, graph_wf, dense
  Test.init_enables_collect (Seq.create heap_size 0uy);
  // init_fp_in_heap proves: fp_in_heap fp0 s0
  Test.init_fp_in_heap (Seq.create heap_size 0uy);
  // empty vertex set properties for empty roots
  Test.empty_coerce ();
  Test.empty_is_vertex_set ();

  // Now gc_precondition s0 Seq.empty fp0 holds
  // and stack_capacity st == heap_size >= heap_size

  // Run mark + sweep with empty roots
  let fp1 = collect heap st fp0;

  // After collect: gc_postcondition holds, giving well_formed_heap
  with s1 st1. assert (is_heap heap s1 ** is_gray_stack st st1);
  SpecGCPost.gc_postcondition_elim s1;

  // Allocate on the post-GC heap (wosize 4)
  let res = allocate heap fp1 4UL;

  // Clean up stack first
  let stack_back = destroy_stack st;
  V.free stack_back;

  // Then drop heap
  with s2. assert (is_heap heap s2);
  drop_ (is_heap heap s2);
}
#pop-options
